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
    'test/DocumentationConsumer/*.lean' 'test/ParliamentConsumer/*.lean'
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

# The `Std.Do` quarantine (AGENTS.md Std.Do quarantine, docs/guides/program-logic.md): core's
# weakest-precondition API moves fast, so it is fenced in two tiers.
#
# * Definitions (`Std.Do` and `Std.Internal.Do`: `WP`, `WPMonad`, `Triple`, spec lemmas) may be
#   imported by the program-logic kernel — `PolyFun/Control/Monad/`, `PolyFun/Control/Do/`,
#   `PolyFun/PFunctor/Free/`, `PolyFun/ITree/Do.lean` — and by the `PolyFunTest/Do/` tests.
# * Tactics (`Std.Tactic.Do`: `mvcgen`, `vcgen`, and the `@[spec]` attribute syntax) stay in
#   `PolyFun/Control/Do/`, `PolyFun/PFunctor/Free/Do.lean`, and `PolyFunTest/Do/`.
#
# `ToCslib/` stages material for cslib, which uses neither stack, so it may import none of it
# directly (cslib's `IsMonadHom` module brings the legacy `Std.Do.WP` classes in transitively;
# the fence is about direct imports and instances). `ComplexityBackends/` sits above PolyFun and
# is likewise outside both tiers. Everything the fenced modules export is a
# construction or a scoped instance, never a global `WP` instance.
std_do_def_allowed() {
  case "$1" in
    PolyFun/Control/Monad/*|PolyFun/Control/Do/*|PolyFun/PFunctor/Free/*|PolyFun/ITree/Do.lean|PolyFunTest/Do/*)
      return 0 ;;
    *) return 1 ;;
  esac
}

std_do_tactic_allowed() {
  case "$1" in
    PolyFun/Control/Do/*|PolyFun/PFunctor/Free/Do.lean|PolyFunTest/Do/*) return 0 ;;
    *) return 1 ;;
  esac
}

import_prefix='^[[:space:]]*(public[[:space:]]+)?(meta[[:space:]]+)?import([[:space:]]+all)?[[:space:]]+'
std_do_def_pattern="${import_prefix}Std\.(Internal\.)?Do([[:space:]]*$|\.)"
std_do_tactic_pattern="${import_prefix}Std\.Tactic\.Do([[:space:]]*$|\.)"

# Keep every supported import modifier covered: otherwise a valid Lean import form can bypass
# the quarantine while the repository's existing files still leave this check green.
for std_do_import in \
    'import Std.Do' \
    'import Std.Internal.Do' \
    'public import Std.Internal.Do.WP.Basic' \
    'import all Std.Do.Triple' \
    'public import all Std.Do' \
    'meta import Std.Do' \
    'public meta import Std.Internal.Do' \
    'meta import all Std.Do' \
    'public meta import all Std.Do'; do
  if ! grep -qE "$std_do_def_pattern" <<< "$std_do_import"; then
    echo "ERROR: Std.Do definition matcher does not recognize: $std_do_import" >&2
    status=1
  fi
done

for std_do_import in \
    'public import Std.Tactic.Do' \
    'import Std.Tactic.Do.Syntax' \
    'import all Std.Tactic.Do' \
    'public import all Std.Tactic.Do' \
    'meta import Std.Tactic.Do' \
    'public meta import Std.Tactic.Do' \
    'meta import all Std.Tactic.Do' \
    'public meta import all Std.Tactic.Do'; do
  if ! grep -qE "$std_do_tactic_pattern" <<< "$std_do_import"; then
    echo "ERROR: Std.Tactic.Do matcher does not recognize: $std_do_import" >&2
    status=1
  fi
done

if grep -qE "$std_do_def_pattern" <<< 'import Std.Tactic.Do'; then
  echo "ERROR: Std.Do definition matcher must not classify tactic imports." >&2
  status=1
fi
if grep -qE "$std_do_tactic_pattern" <<< 'import Std.Internal.Do'; then
  echo "ERROR: Std.Tactic.Do matcher must not classify definition imports." >&2
  status=1
fi

while IFS= read -r file; do
  if grep -qE "$std_do_def_pattern" "$file" && ! std_do_def_allowed "$file"; then
    echo "ERROR: $file imports core Std.Do / Std.Internal.Do outside the quarantine." >&2
    echo "Only the program-logic kernel (PolyFun/Control/Monad/, PolyFun/Control/Do/," >&2
    echo "PolyFun/PFunctor/Free/, PolyFun/ITree/Do.lean) and PolyFunTest/Do/ may depend on" >&2
    echo "it. See AGENTS.md Std.Do quarantine." >&2
    status=1
  fi
  if grep -qE "$std_do_tactic_pattern" "$file" && ! std_do_tactic_allowed "$file"; then
    echo "ERROR: $file imports core Std.Tactic.Do outside the quarantine." >&2
    echo "Only PolyFun/Control/Do/, PolyFun/PFunctor/Free/Do.lean, and PolyFunTest/Do/ may" >&2
    echo "depend on it. See AGENTS.md Std.Do quarantine." >&2
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

if (( status != 0 )); then
  exit "$status"
fi

echo "✓ Module scopes and Interaction API boundaries are valid."
