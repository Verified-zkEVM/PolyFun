"""Quote raw typed-AST data for kernel-checked import certificates.

This module performs constructor serialization only. It does not specialize,
type-check, normalize, or compile a source expression. export_cases.py owns
regeneration and byte-for-byte checks against the pinned Haskell export.
"""

import json
import re


def string(value):
    return json.dumps(value, ensure_ascii=False)


def array(values):
    return "[" + ", ".join(values) + "]"


def app(constructor, *arguments):
    return "(" + constructor + (" " if arguments else "") + " ".join(arguments) + ")"


def name(value):
    return app("Reference.Name.mk", str(value["id"]), string(value["text"]),
               string(value["origin"]))


def parameter(value):
    kind = {"num": "number", "type": "value", "prop": "proposition"}[value["kind"]["tag"]]
    return app("Reference.Parameter.mk", str(value["id"]), "." + kind)


def type_expr(value):
    tag, args = value["tag"], value["args"]
    if tag == "var":
        return app(".var", parameter(args[0]))
    if tag == "num":
        return app(".number", str(int(args[0])))
    if tag == "con":
        return app(".constructor", string(args[0]), array(map(type_expr, args[1])))
    if tag == "synonym":
        return app(".synonym", name(args[0]), array(map(type_expr, args[1])), type_expr(args[2]))
    if tag == "nominal":
        return app(".nominal", name(args[0]), array(map(type_expr, args[1])))
    if tag == "tuple":
        return app(".tuple", str(args[0]), array(map(type_expr, args[1])))
    if tag == "record":
        return app(".record", array(app("Prod.mk", string(k), type_expr(t)) for k, t in args[0]))
    if tag == "has":
        return app(".has", selector(args[0]), array(map(type_expr, args[1])))
    raise ValueError(f"unhandled raw type constructor: {tag}")


def schema(value):
    return app("Reference.Schema.mk", array(map(parameter, value["parameters"])),
               array(map(type_expr, value["constraints"])), type_expr(value["body"]))


def selector(value):
    tag, (index, shape) = value["tag"], value["args"]
    if tag == "record":
        return app(".record", string(index), ".none" if shape is None else
                   app(".some", array(map(string, shape))))
    if tag in {"tuple", "list"}:
        return app("." + tag, str(index), ".none" if shape is None else app(".some", str(shape)))
    raise ValueError(f"unhandled selector: {tag}")


def expression(value):
    tag, args = value["tag"], value["args"]
    if tag == "var":
        return app(".var", name(args[0]))
    if tag == "app":
        return app(".app", expression(args[0]), expression(args[1]))
    if tag == "abs":
        return app(".abs", name(args[0]), type_expr(args[1]), expression(args[2]))
    if tag == "typeAbs":
        return app(".typeAbs", parameter(args[0]), expression(args[1]))
    if tag == "typeApp":
        return app(".typeApp", expression(args[0]), type_expr(args[1]))
    if tag == "proofAbs":
        return app(".proofAbs", type_expr(args[0]), expression(args[1]))
    if tag == "proofApp":
        return app(".proofApp", expression(args[0]))
    if tag == "where":
        return app(".whereE", expression(args[0]), array(map(group, args[1])))
    if tag == "list":
        return app(".list", type_expr(args[0]), array(map(expression, args[1])))
    if tag == "if":
        return app(".ite", *map(expression, args))
    if tag == "case":
        return app(".caseE", expression(args[0]), array(
            app("Prod.mk", string(k), case_alt(a)) for k, a in args[1]),
            ".none" if args[2] is None else app(".some", case_alt(args[2])))
    if tag == "update":
        return app(".update", type_expr(args[0]), expression(args[1]),
                   selector(args[2]), expression(args[3]))
    if tag == "guards":
        return app(".guards", type_expr(args[0]), array(
            app("Prod.mk", array(map(type_expr, cs)), expression(e)) for cs, e in args[1]))
    if tag == "tuple":
        return app(".tuple", array(map(expression, args[0])))
    if tag == "record":
        return app(".record", array(app("Prod.mk", string(k), expression(e)) for k, e in args[0]))
    if tag == "select":
        return app(".select", expression(args[0]), selector(args[1]))
    if tag == "comprehension":
        return app(".comprehension", type_expr(args[0]), type_expr(args[1]), expression(args[2]),
                   array(array(map(match_expr, branch)) for branch in args[3]))
    raise ValueError(f"unhandled raw expression constructor: {tag}")


def case_alt(value):
    return app("Reference.CaseAlt.mk", array(
        app("Prod.mk", name(n), type_expr(t)) for n, t in value["bindings"]),
        expression(value["body"]))


def match_expr(value):
    tag, args = value["tag"], value["args"]
    if tag == "from":
        return app(".from", name(args[0]), type_expr(args[1]), type_expr(args[2]), expression(args[3]))
    if tag == "let":
        return app(".letE", declaration(args[0]))
    raise ValueError(f"unhandled match: {tag}")


def declaration(value):
    definition = value["definition"]
    if definition["tag"] == "primitive":
        body = ".primitive"
    elif definition["tag"] == "expression":
        body = app(".expression", expression(definition["args"][0]))
    elif definition["tag"] == "foreign":
        interface, fallback = definition["args"]
        body = app(".foreign", string(interface), ".none" if fallback is None else
                   app(".some", expression(fallback)))
    else:
        raise ValueError("unsupported raw declaration form")
    return app("Reference.Decl.mk", name(value["name"]), schema(value["schema"]), body)


def group(value):
    if value["tag"] == "nonrecursive":
        return app(".nonrecursive", declaration(value["args"][0]))
    if value["tag"] == "recursive":
        return app(".recursive", array(map(declaration, value["args"][0])))
    raise ValueError("unsupported declaration group")


def wrap(source):
    # String literals stay indivisible; layout is otherwise irrelevant inside parentheses.
    tokens = re.findall(r'"(?:\\.|[^"\\])*"|[^\s"]+', source)
    lines, line = [], "  "
    for token in tokens:
        if len(line) + len(token) + 1 > 98 and line.strip():
            lines.append(line.rstrip())
            line = "  "
        line += token + " "
    return "\n".join(lines + [line.rstrip()])


def quote_bundle(bundle, *, namespace, artifact, title, driver,
                 copyright="PolyFun Contributors", authors="Devon Tuma"):
    """Quote a closed single-root bundle without semantic normalization.

    `namespace` is the complete Lean namespace; `artifact` and `driver` are the
    repository-relative JSON input and regeneration script named in the docstring.
    """
    assert bundle["roots"] and not bundle["primitive_fallbacks"]
    declarations = []
    for group in bundle["groups"]:
        assert group["tag"] == "nonrecursive"
        declarations.append(declaration(group["args"][0]))
    modules = [app("SourceModule.mk", string(m["name"]), string(m["path"]),
                   string(m["sha256"]), array(app("Prod.mk", name(n), string(a))
                                             for n, a in m["aliases"])) for m in bundle["modules"]]
    source = f'''/-
Copyright (c) 2026 {copyright}. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: {authors}
-/

module

public import PolyFunCryptol.Translation.SourceBundle

/-!
# {title}

Raw constructor data from `{artifact}`, including
source identities, schemes and annotations. `{driver}`
checks byte-for-byte reproduction from the pinned official frontend.
-/

public section

namespace {namespace}

open Cryptol Translation

'''
    for i, d in enumerate(declarations):
        source += f'/-- Source declaration {i + 1} in dependency order. -/\n'
        source += f'@[expose] def declaration{i} : Reference.Decl :=\n{wrap(d)}\n\n'
    roots = []
    for i, root in enumerate(bundle['roots']):
        roots.append('root' if len(bundle['roots']) == 1 else f'root{i}')
        source += '/-- The official frontend\'s fully instantiated entry point. -/\n'
        source += f'@[expose] def {roots[-1]} : SourceRoot :=\n' + wrap(app(
            'SourceRoot.mk', string(root['text']), expression(root['expression']),
            schema(root['schema']))) + '\n\n'
    groups = array(app('.nonrecursive', f'declaration{i}') for i in range(len(declarations)))
    source += '/-- The exact exported scalar bundle, retaining its provenance metadata. -/\n'
    source += '@[expose] def bundle : SourceBundle :=\n' + wrap(app(
        'SourceBundle.mk', string(bundle['cryptol_revision']), array(roots), groups,
        array(modules), '[]', array(map(string, bundle.get('frontend_patches', []))))) + \
        f'\n\nend {namespace}\n'
    return source.encode()


def source_module(value):
    return app("SourceModule.mk", string(value["name"]), string(value["path"]),
               string(value["sha256"]), array(app("Prod.mk", name(n), string(a))
                                             for n, a in value["aliases"]))


def source_location(value):
    pair = lambda xs: app("Prod.mk", *map(str, xs))
    return app("SourceLocation.mk", string(value["source_basename"]),
               pair(value["start"]), pair(value["end"]))


def declaration_info(value):
    key = value["source_key"]
    identity = app("SourceIdentity.mk", ".none" if key["module"] is None else
                   app(".some", string(key["module"])), string(key["name"]),
                   source_location(key["location"]))
    return app("DeclarationInfo.mk", name(value["name"]), identity,
               array(map(name, value["dependencies"])), str(value["property"]).lower())
