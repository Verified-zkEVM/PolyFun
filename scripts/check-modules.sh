#!/usr/bin/env bash

# Check repository-wide Lean module-scope invariants.

set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"

status=0

# Lean sources in the production, tutorial and test libraries, plus the external consumer.
lean_sources() {
  git ls-files -- 'PolyFun.lean' 'PolyFun/*.lean' 'ToCslib.lean' 'ToCslib/*.lean' \
    'ComplexityBackends.lean' 'ComplexityBackends/*.lean' 'PolyFunTest/*.lean' \
    'Examples/*.lean' 'PolyFunParliamentMain.lean' \
    'test/DocumentationConsumer/*.lean' 'test/ParliamentConsumer/*.lean' 'PolyFunFrontier/*.lean'
}

while IFS= read -r file; do
  if ! grep -qx 'module' "$file"; then
    echo "ERROR: $file does not enable module mode with a 'module' command." >&2
    status=1
  fi
done < <(lean_sources)

while IFS= read -r file; do
  if ! grep -qx 'public section' "$file"; then
    echo "ERROR: $file does not declare its Interaction API in a 'public section'." >&2
    status=1
  fi
done < <(git ls-files -- 'PolyFun/Interaction/*.lean')

# Core program-logic rules (AGENTS.md, docs/guides/program-logic.md). Two of the four rules are
# textual and are checked here. `PolyFunTest/Policy/WP.lean` checks the other two on the elaborated
# environment: no global `WP`, `WPMonad`, `MAlgOrdered` or `MAlgRelOrdered` instance, and a global
# `@[spec]` registration only for a rule on its allowlist.
#
# * Imports: `ToCslib/` stages material for cslib, which uses neither of core's weakest-precondition
#   frameworks, so it imports no module of `Std.WP`, `Std.Do`, the pre-4.35 `Std.Internal.Do`, or
#   `Std.Tactic.Do` directly. cslib's `IsMonadHom` module brings core's `Std.Do.WP` classes in
#   transitively; the rule is about direct imports. Every other library may import them.
# * Tactics: core marks `vcgen` experimental and `mvcgen` deprecated, so only the tests under
#   `PolyFunTest/` call them or set `experimental.vcgen`. Elsewhere they may appear in comments and
#   docstrings only.
import_prefix='^[[:space:]]*(public[[:space:]]+)?(meta[[:space:]]+)?import([[:space:]]+all)?[[:space:]]+'
core_wp_pattern="${import_prefix}Std\.(WP|Do|Internal\.Do|Tactic\.Do)([[:space:]]|\.|$)"

# Keep every import modifier and every module family covered: otherwise a valid Lean import form
# could bypass the rule while the repository's existing files still leave this check green.
for core_wp_import in \
    'import Std.WP' \
    'public import Std.WP.Monad.Basic' \
    'import all Std.WP.Triple' \
    'import Std.WP.EPostSlot' \
    'meta import Std.WP.Tactic' \
    'import Std.WP -- for the triples' \
    'import Std.Do' \
    'import all Std.Do.Triple' \
    'public import all Std.Do' \
    'meta import all Std.Do' \
    'import Std.Internal.Do' \
    'public import Std.Internal.Do.WP.Basic' \
    'public meta import Std.Internal.Do' \
    'public import Std.Tactic.Do' \
    'import Std.Tactic.Do.Syntax' \
    'public meta import all Std.Tactic.Do'; do
  if ! grep -qE "$core_wp_pattern" <<< "$core_wp_import"; then
    echo "ERROR: core program-logic import matcher does not recognize: $core_wp_import" >&2
    status=1
  fi
done
for other_import in \
    'import Std.Data.HashMap' \
    'import Std.Tactic.BVDecide' \
    'import Std.WPExtra' \
    'import Std.Doc' \
    '-- import Std.WP' \
    'import Mathlib.Std.WP'; do
  if grep -qE "$core_wp_pattern" <<< "$other_import"; then
    echo "ERROR: core program-logic import matcher must not classify: $other_import" >&2
    status=1
  fi
done

while IFS= read -r file; do
  if grep -qE "$core_wp_pattern" "$file"; then
    echo "ERROR: $file imports core's Std.WP, Std.Do or Std.Tactic.Do from the ToCslib staging" >&2
    echo "library. See AGENTS.md, \"Core program-logic rules\"." >&2
    status=1
  fi
done < <(git ls-files -- 'ToCslib.lean' 'ToCslib/*.lean')

# Lean code with its comments and docstrings removed: nested `/- … -/` blocks, innermost first,
# then `--` line comments. String literals are not parsed.
lean_code() {
  perl -0777 -pe '1 while s{/-(?:(?!/-|-/).)*-/}{}gs; s{--[^\n]*}{}g'
}
vcgen_pattern='(^|[^[:alnum:]_])m?vcgen([^[:alnum:]_]|$)'

# Whether the Lean source on standard input calls `vcgen` or `mvcgen` or sets
# `experimental.vcgen`. The code is captured first so that `grep -q` cannot cut the pipe short.
uses_vcgen() {
  local code
  code="$(lean_code)"
  grep -qE "$vcgen_pattern" <<< "$code"
}

for vcgen_use in \
    $'example : True := by\n  vcgen [logPair]' \
    '  vcgen -errorOnMissingSpec [prog] <;> simp_all' \
    '  · vcgen?' \
    '  mvcgen' \
    'set_option experimental.vcgen true in' \
    $'/-- A triple. -/\ntheorem t : True := by vcgen'; do
  if ! uses_vcgen <<< "$vcgen_use"; then
    echo "ERROR: vcgen matcher does not recognize: $vcgen_use" >&2
    status=1
  fi
done
for vcgen_mention in \
    '-- vcgen [logPair]' \
    '/-- Rules that let `vcgen` decompose free programs. -/' \
    $'/-!\n# Rules for `vcgen`\n\n`mvcgen` is deprecated.\n-/' \
    '/- outer /- inner -/ then `vcgen` -/' \
    'theorem t : True := trivial -- not by `vcgen`' \
    'attribute [vcgen_simp] foo' \
    'open Lean.Elab.Tactic.VCGen' \
    'def vcgenRules := 0'; do
  if uses_vcgen <<< "$vcgen_mention"; then
    echo "ERROR: vcgen matcher must not classify: $vcgen_mention" >&2
    status=1
  fi
done

while IFS= read -r file; do
  case "$file" in PolyFunTest/*) continue ;; esac
  if uses_vcgen < "$file"; then
    echo "ERROR: $file calls vcgen or mvcgen, or sets experimental.vcgen, outside PolyFunTest/." >&2
    echo "Prove library lemmas from the spec lemmas directly. See AGENTS.md, \"Core program-logic" >&2
    echo "rules\"." >&2
    status=1
  fi
done < <(lean_sources)

# PMF bridges (docs/guides/probability.md): measure interpretations use Mathlib's `Measure` and
# `Kernel`, not its probability mass functions. Only a PMF bridge imports
# `Mathlib.Probability.ProbabilityMassFunction`, and only its `Basic` or `Monad` module:
# `Constructions`, which holds the lawful monad instance on `PMF`, brings in most of Mathlib's
# analysis. A bridge is a module `<M>/PMF.lean` beside a tracked module `<M>.lean`, by convention
# the measure module whose construction it relates to `PMF`; the check does not read `<M>.lean`.
# Like the core program-logic import rule, these checks read direct imports only: a Mathlib module
# that imports `Constructions`, such as `Mathlib.Probability.Distributions.Uniform`, passes them.
pmf_bridge_path() {
  case "$1" in
    */*/PMF.lean) return 0 ;;
    *) return 1 ;;
  esac
}
# The module `<M>.lean` that the bridge `<M>/PMF.lean` sits beside.
pmf_bridge_sibling() {
  printf '%s.lean' "${1%/PMF.lean}"
}
pmf_pattern="${import_prefix}Mathlib\.Probability\.ProbabilityMassFunction([[:space:]]|\.|$)"
pmf_light_pattern="${import_prefix}Mathlib\.Probability\.ProbabilityMassFunction\.(Basic|Monad)([[:space:]]|$)"

for pmf_import in \
    'import Mathlib.Probability.ProbabilityMassFunction.Constructions' \
    'public import Mathlib.Probability.ProbabilityMassFunction.Basic' \
    'meta import Mathlib.Probability.ProbabilityMassFunction.Monad' \
    'public meta import all Mathlib.Probability.ProbabilityMassFunction'; do
  if ! grep -qE "$pmf_pattern" <<< "$pmf_import"; then
    echo "ERROR: probability-mass-function matcher does not recognize: $pmf_import" >&2
    status=1
  fi
done
for other_import in 'import Mathlib.Probability.Kernel.Basic' 'import Mathlib.Probability.UniformOn' \
    'import Mathlib.Probability.ProbabilityMassFunctionExtra'; do
  if grep -qE "$pmf_pattern" <<< "$other_import"; then
    echo "ERROR: probability-mass-function matcher must not classify: $other_import" >&2
    status=1
  fi
done
for light_import in 'public import Mathlib.Probability.ProbabilityMassFunction.Basic' \
    'import Mathlib.Probability.ProbabilityMassFunction.Monad -- bind'; do
  if ! grep -qE "$pmf_light_pattern" <<< "$light_import"; then
    echo "ERROR: PMF bridge import matcher does not allow: $light_import" >&2
    status=1
  fi
done
for heavy_import in 'import Mathlib.Probability.ProbabilityMassFunction.Constructions' \
    'import Mathlib.Probability.ProbabilityMassFunction.Integrals' \
    'import Mathlib.Probability.ProbabilityMassFunction.Basic.Extra' \
    'import Mathlib.Probability.ProbabilityMassFunction'; do
  if grep -qE "$pmf_light_pattern" <<< "$heavy_import"; then
    echo "ERROR: PMF bridge import matcher must not allow: $heavy_import" >&2
    status=1
  fi
done
for bridge in \
    'ToCslib/Probability/UniformOn/PMF.lean' \
    'PolyFun/PFunctor/Free/Measure/PMF.lean' \
    'PolyFunTest/Probability/Uniform/PMF.lean'; do
  if ! pmf_bridge_path "$bridge"; then
    echo "ERROR: PMF bridge matcher does not recognize: $bridge" >&2
    status=1
  fi
done
for non_bridge in \
    'PolyFun.lean' \
    'PolyFun/PMF.lean' \
    'PolyFunTest/PMF.lean' \
    'ToCslib/Probability/UniformOn.lean' \
    'ToCslib/Probability/UniformOn/PMFBridge.lean' \
    'ToCslib/Probability/UniformOn/PMF/Extra.lean'; do
  if pmf_bridge_path "$non_bridge"; then
    echo "ERROR: PMF bridge matcher must reject: $non_bridge" >&2
    status=1
  fi
done
if [[ "$(pmf_bridge_sibling 'ToCslib/Probability/UniformOn/PMF.lean')" \
    != 'ToCslib/Probability/UniformOn.lean' ]]; then
  echo "ERROR: PMF bridge sibling does not name the module beside the bridge." >&2
  status=1
fi

while IFS= read -r file; do
  if ! grep -qE "$pmf_pattern" "$file"; then
    continue
  fi
  if ! pmf_bridge_path "$file"; then
    echo "ERROR: $file imports Mathlib's probability mass functions outside a PMF bridge." >&2
    echo "Use Measure and Kernel, or relate a measure module <M>.lean to PMF in <M>/PMF.lean." >&2
    echo "See docs/guides/probability.md, \"Where the modules live\"." >&2
    status=1
    continue
  fi
  sibling="$(pmf_bridge_sibling "$file")"
  if [[ -z "$(git ls-files -- "$sibling")" ]]; then
    echo "ERROR: PMF bridge $file has no module $sibling beside it." >&2
    status=1
  fi
  if grep -E "$pmf_pattern" "$file" | grep -qvE "$pmf_light_pattern"; then
    echo "ERROR: PMF bridge $file imports a module of Mathlib's probability mass functions" >&2
    echo "other than Basic and Monad. See docs/guides/probability.md." >&2
    status=1
  fi
done < <(lean_sources)

if grep -rEn --include='*.lean' '@\[expose\][[:space:]]+public section' PolyFun/Interaction; then
  echo "ERROR: Broad exposed public sections are forbidden in PolyFun/Interaction." >&2
  echo "Expose individual definitions, or use 'import all' in proof modules." >&2
  status=1
fi

# Production and upstream staging must stay usable without teaching/test libraries or executables.
while IFS= read -r file; do
  if grep -qE "${import_prefix}(Examples|PolyFunTest|PolyFunParliamentMain)([[:space:]]|\.|$)" "$file"; then
    echo "ERROR: $file imports an example, test, or executable from a production library." >&2
    status=1
  fi
done < <(git ls-files -- 'PolyFun.lean' 'PolyFun/*.lean' 'ToCslib.lean' 'ToCslib/*.lean' \
  'ComplexityBackends.lean' 'ComplexityBackends/*.lean')

# Layering (docs/reference/repo-map.md): `ToCslib` is upstream staging and never imports PolyFun or
# a complexity backend; the generic `PolyFun` library never imports a concrete complexity backend.
while IFS= read -r file; do
  if grep -qE "${import_prefix}(PolyFun|ComplexityBackends)([[:space:]]|\.|$)" "$file"; then
    echo "ERROR: $file imports PolyFun or ComplexityBackends from the ToCslib staging library." >&2
    status=1
  fi
done < <(git ls-files -- 'ToCslib.lean' 'ToCslib/*.lean')

while IFS= read -r file; do
  if grep -qE "${import_prefix}ComplexityBackends([[:space:]]|\.|$)" "$file"; then
    echo "ERROR: $file imports a concrete complexity backend from the generic PolyFun library." >&2
    status=1
  fi
done < <(git ls-files -- 'PolyFun.lean' 'PolyFun/*.lean')

# The cslib-frontier square (PolyFunFrontier/README.md): PolyFun requires Mathlib and CSLib only,
# and cslib-frontier enters through the nested `PolyFunFrontier/` package alone. No module outside
# it imports `CslibFrontier` or `PolyFunFrontier`, and the root package never requires
# cslib-frontier, so `import PolyFun` and PolyFun's dependents never resolve it.
frontier_pattern="${import_prefix}(CslibFrontier|PolyFunFrontier)([[:space:]]|\.|$)"
for frontier_import in \
    'import CslibFrontier' \
    'public import CslibFrontier.Computability.DecisionTree.Parity' \
    'import all PolyFunFrontier.PFunctor.Free.DecisionTree' \
    'public meta import PolyFunFrontier'; do
  if ! grep -qE "$frontier_pattern" <<< "$frontier_import"; then
    echo "ERROR: the cslib-frontier fence does not match '$frontier_import'." >&2
    status=1
  fi
done
for other_import in 'import CslibFrontierExtras' 'import Cslib.Foundations.Data.PFunctor.Free' \
    '-- import CslibFrontier'; do
  if grep -qE "$frontier_pattern" <<< "$other_import"; then
    echo "ERROR: the cslib-frontier fence wrongly matches '$other_import'." >&2
    status=1
  fi
done

while IFS= read -r file; do
  case "$file" in PolyFunFrontier/*) continue ;; esac
  if grep -qE "$frontier_pattern" "$file"; then
    echo "ERROR: $file imports cslib-frontier or PolyFunFrontier outside PolyFunFrontier/." >&2
    status=1
  fi
done < <(git ls-files -- '*.lean')

if grep -qiE 'cslib-frontier|CslibFrontier' lakefile.toml lake-manifest.json; then
  echo "ERROR: the root package names cslib-frontier; only PolyFunFrontier/ may require it." >&2
  status=1
fi

# `import all` boundaries (docs/development/module-api.md, "Who may open whose bodies"): bodies are
# opened only inside the library that owns them. Tests may open a complexity backend; nothing opens a
# backend from the generic library, staging, examples, or consumers; a backend never opens `PolyFun`
# or `ToCslib`; tests reach `PolyFun` through its public API except the grandfathered worked
# examples listed below; ordinary-import canaries open nothing.
import_all_prefix='^[[:space:]]*(public[[:space:]]+)?(meta[[:space:]]+)?import[[:space:]]+all[[:space:]]+'

for import_all_form in \
    'import all ComplexityBackends.CslibSingleTape.Counting' \
    'public import all ComplexityBackends' \
    'meta import all ComplexityBackends.CslibSingleTape.PPoly' \
    'public meta import all ComplexityBackends'; do
  if ! grep -qE "${import_all_prefix}ComplexityBackends([[:space:]]|\.|$)" <<< "$import_all_form"; then
    echo "ERROR: import-all matcher does not recognize: $import_all_form" >&2
    status=1
  fi
done
if grep -qE "${import_all_prefix}PolyFun([[:space:]]|\.|$)" <<< 'import all PolyFunTest.Realizability.Quantitative'; then
  echo "ERROR: import-all matcher must not classify PolyFunTest imports as PolyFun imports." >&2
  status=1
fi

# The "opens nothing" rules below match the bare prefix, so it must accept every import-all
# modifier and reject ordinary imports and the `-- import all:` annotation comments that record
# which definitions an opened body supplies.
for import_all_form in \
    'import all PolyFun.Interaction.Basic.Shape' \
    'public import all ToCslib.Order.Basic' \
    'meta import all Mathlib.Tactic' \
    'public meta import all ComplexityBackends.CslibSingleTape.Basic'; do
  if ! grep -qE "${import_all_prefix}" <<< "$import_all_form"; then
    echo "ERROR: bare import-all matcher does not recognize: $import_all_form" >&2
    status=1
  fi
done

for ordinary_form in \
    'import PolyFun.Interaction.Basic.Shape' \
    'public import ToCslib.Order.Basic' \
    'meta import Mathlib.Tactic' \
    '-- import all: unfolds `par_route_left`' \
    'import allocation.Basic'; do
  if grep -qE "${import_all_prefix}" <<< "$ordinary_form"; then
    echo "ERROR: bare import-all matcher must not classify: $ordinary_form" >&2
    status=1
  fi
done

# No file opens an external library (Lean core, Std, Batteries, Mathlib, CSLib or any other
# dependency). Bodies are opened only inside the library that owns them, and this repository owns
# none of its dependencies; a body that module mode hides must be reached through a public
# equation. `import all` may name only this repository's own libraries.
own_library_pattern="${import_all_prefix}(PolyFun[[:alnum:]_]*|ToCslib|ComplexityBackends|Examples)([[:space:]]|\.|$)"

opens_external_library() {
  local opened
  opened=$(grep -E "${import_all_prefix}" | grep -vE "$own_library_pattern" || true)
  [[ -n "$opened" ]]
}

for external_form in \
    'import all Mathlib.Data.List.Sort' \
    'public import all Batteries.Data.List.Basic' \
    'meta import all Init.Data.List.Sort.Basic' \
    'public meta import all Lean.Elab.Command' \
    'import all Std.Data.HashMap' \
    'import all Cslib.Foundations.Data.FreeM'; do
  if ! opens_external_library <<< "$external_form"; then
    echo "ERROR: external-library matcher does not recognize: $external_form" >&2
    status=1
  fi
done

for own_form in \
    'import all PolyFun.IPFunctor.Scoped.Basic' \
    'import all PolyFunTest.Realizability.Quantitative' \
    'public import all ToCslib.Order.Basic' \
    'meta import all ComplexityBackends.CslibSingleTape.Counting' \
    'import all Examples.Tutorials.Requests' \
    'import Mathlib.Data.List.Sort' \
    '-- import all Mathlib.Data.List.Sort'; do
  if opens_external_library <<< "$own_form"; then
    echo "ERROR: external-library matcher must not classify: $own_form" >&2
    status=1
  fi
done

while IFS= read -r file; do
  if opens_external_library < "$file"; then
    echo "ERROR: $file uses 'import all' on an external library. Reach a hidden body through a" >&2
    echo "public equation instead; only this repository's own libraries may be opened." >&2
    status=1
  fi
done < <(git ls-files -- '*.lean')

backend_import_all_allowed() {
  case "$1" in
    PolyFunTest/ModuleAPI/*) return 1 ;;
    ComplexityBackends/*|PolyFunTest/*) return 0 ;;
    *) return 1 ;;
  esac
}

while IFS= read -r file; do
  if grep -qE "${import_all_prefix}ComplexityBackends([[:space:]]|\.|$)" "$file" \
      && ! backend_import_all_allowed "$file"; then
    echo "ERROR: $file uses 'import all' on a complexity backend outside ComplexityBackends/ and" >&2
    echo "PolyFunTest/ (module canaries excluded)." >&2
    status=1
  fi
done < <(lean_sources)

while IFS= read -r file; do
  if grep -qE "${import_all_prefix}(PolyFun|ToCslib)([[:space:]]|\.|$)" "$file"; then
    echo "ERROR: $file opens PolyFun or ToCslib bodies from a complexity backend." >&2
    status=1
  fi
done < <(git ls-files -- 'ComplexityBackends.lean' 'ComplexityBackends/*.lean')

# `ToCslib` opens nothing. Staging modules are meant to be lifted into cslib unchanged, and cslib
# has no access to this repository's bodies, so a proof that needs an opened body is not portable.
while IFS= read -r file; do
  if grep -qE "${import_all_prefix}" "$file"; then
    echo "ERROR: $file uses 'import all' from the ToCslib staging library, which stays" >&2
    echo "ordinary-import clean so its modules can be upstreamed unchanged." >&2
    status=1
  fi
done < <(git ls-files -- 'ToCslib.lean' 'ToCslib/*.lean')

# Tutorials, the case-study executable and the external consumer packages open nothing. They are
# the evidence that the ordinary-import surface is usable; opening a body would let a public
# equation regress without any check noticing.
while IFS= read -r file; do
  if grep -qE "${import_all_prefix}" "$file"; then
    echo "ERROR: $file uses 'import all'; tutorials, the executable entry point and the consumer" >&2
    echo "packages must reach every library through its public API." >&2
    status=1
  fi
done < <(git ls-files -- 'Examples/*.lean' 'PolyFunParliamentMain.lean' \
  'test/DocumentationConsumer/*.lean' 'test/ParliamentConsumer/*.lean')

# Grandfathered worked examples that still open `PolyFun` bodies. Remove entries as they migrate to
# public laws; do not add entries.
test_import_all_polyfun_allowed() {
  case "$1" in
    PolyFunTest/Interaction/Basic/ChainAppendExamples.lean|\
    PolyFunTest/Interaction/Basic/ChainExamples.lean|\
    PolyFunTest/Interaction/Basic/FoundationNormalization.lean|\
    PolyFunTest/Interaction/Concurrent/Examples.lean|\
    PolyFunTest/Interaction/Multiparty/Examples.lean|\
    PolyFunTest/Interaction/Open/EmulatesFactorizationExamples.lean|\
    PolyFunTest/Interaction/Open/OpenProcessActivationExamples.lean|\
    PolyFunTest/Interaction/Open/OpenProcessCoherenceExamples.lean|\
    PolyFunTest/Interaction/Open/SubTheoryExamples.lean|\
    PolyFunTest/Interaction/TwoParty/Examples.lean) return 0 ;;
    *) return 1 ;;
  esac
}

while IFS= read -r file; do
  if grep -qE "${import_all_prefix}PolyFun([[:space:]]|\.|$)" "$file" \
      && ! test_import_all_polyfun_allowed "$file"; then
    echo "ERROR: $file uses 'import all' on PolyFun from a test that is not a grandfathered" >&2
    echo "worked example; reach the generic library through its public API." >&2
    status=1
  fi
done < <(git ls-files -- 'PolyFunTest/*.lean')

while IFS= read -r file; do
  if grep -qE "${import_all_prefix}" "$file"; then
    echo "ERROR: $file is an ordinary-import canary and may not use 'import all'." >&2
    status=1
  fi
done < <(git ls-files -- 'PolyFunTest/ModuleAPI/*.lean')

# Imported declarations reach the kernel only through `IPFunctor.Import.submit`, which turns off
# asynchronous checking and `debug.skipKernelTC`, applies the per-declaration budget, and restores
# the environment after a rejection so that no fallback axiom remains. In the import machinery and
# its tests, only `Import/Submit.lean` adds declarations. The pattern names the functions that add
# a declaration: `addDecl`, `addAndCompile`, the auxiliary-declaration helpers `mkAuxLemma`,
# `mkAuxTheorem`, `mkAuxDefinition` and `mkAuxDefinitionFor`, and the kernel's `addDeclCore` and
# `addDeclWithoutChecking`, which skip the check (`addDeclCore` when `doCheck := false`). Every
# mention of `addDeclCore` is rejected, whatever its arguments, because the flag can be passed
# positionally or through a variable. The match is textual, so a declaration added by another
# route, such as elaborating a command, is outside it.
import_add_pattern='(^|[^[:alnum:]_])(addDecl|addDeclCore|addDeclWithoutChecking|addAndCompile|mkAuxLemma|mkAuxTheorem|mkAuxDefinition|mkAuxDefinitionFor)([^[:alnum:]_]|$)'

for add_form in \
    'addDecl decl' \
    '  atomically <| withOptions (guard b) <| addDecl decl (forceExpose := forceExpose)' \
    '  return env.addDecl (guard b (← getOptions)) decl' \
    '  discard <| mkAuxLemma [] type value' \
    'addAndCompile d' \
    '  return env.addDeclWithoutChecking decl' \
    '  setEnv (← ofExceptKernelException <| (← getEnv).addDeclCore 0 0 decl none (doCheck := false))' \
    '  let env ← ofExceptKernelException (Kernel.Environment.addDeclCore env 0 0 decl none)' \
    '  discard <| mkAuxTheorem type value' \
    '  let c ← mkAuxDefinition name type value' \
    '  let c ← mkAuxDefinitionFor name value'; do
  if ! grep -qE "$import_add_pattern" <<< "$add_form"; then
    echo "ERROR: import addDecl matcher does not recognize: $add_form" >&2
    status=1
  fi
done

for other_form in \
    '  submit (← reflDecl name lhs rhs) cfg.budget' \
    'def addDeclaration := 0' \
    'readdDeclared' \
    '  addDeclarationRanges name stx' \
    '  let n ← mkAuxName base 1' \
    '  discard <| mkAuxTheoremLike type'; do
  if grep -qE "$import_add_pattern" <<< "$other_form"; then
    echo "ERROR: import addDecl matcher must not classify: $other_form" >&2
    status=1
  fi
done

while IFS= read -r file; do
  case "$file" in
    */Import/Submit.lean) continue ;;
  esac
  if grep -qE "$import_add_pattern" "$file"; then
    echo "ERROR: $file adds declarations directly; the import machinery and its tests go through" >&2
    echo "IPFunctor.Import.submit (PolyFun/IPFunctor/Scoped/Import/Submit.lean)." >&2
    status=1
  fi
done < <(git ls-files -- 'PolyFun/IPFunctor/Scoped/Import/*.lean' \
  'PolyFunTest/IPFunctor/Scoped/Import/*.lean')

if (( status != 0 )); then
  exit "$status"
fi

echo "✓ Module scopes and Interaction API boundaries are valid."
