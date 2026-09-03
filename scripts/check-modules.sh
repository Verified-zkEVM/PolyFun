#!/usr/bin/env bash

# Check repository-wide Lean module-scope invariants.

set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"

status=0

lean_sources() {
  git ls-files -- 'PolyFun.lean' 'PolyFun/*.lean' 'ToCslib.lean' 'ToCslib/*.lean' 'PolyFunTest/*.lean'
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

# The `Std.Do` quarantine (AGENTS.md gotcha 8, docs/wiki/program-logic.md): core's
# weakest-precondition API moves fast, so it is fenced in two tiers.
#
# * Definitions (`Std.Do` and `Std.Internal.Do`: `WP`, `WPMonad`, `Triple`, spec lemmas) may be
#   imported by the program-logic kernel — `PolyFun/Control/Monad/`, `PolyFun/Control/Do/`,
#   `PolyFun/PFunctor/Free/`, `PolyFun/ITree/Do.lean` — and by the `PolyFunTest/Do/` tests.
# * Tactics (`Std.Tactic.Do`: `mvcgen`, `vcgen`, and the `@[spec]` attribute syntax) stay in
#   `PolyFun/Control/Do/`, `PolyFun/PFunctor/Free/Do.lean`, and `PolyFunTest/Do/`.
#
# `ToCslib/` stages material for cslib, which uses neither stack, so it may import none of it.
# Everything the fenced modules export is a construction or a scoped instance, never a global
# `WP` instance.
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
    echo "it. See AGENTS.md gotcha 8." >&2
    status=1
  fi
  if grep -qE "$std_do_tactic_pattern" "$file" && ! std_do_tactic_allowed "$file"; then
    echo "ERROR: $file imports core Std.Tactic.Do outside the quarantine." >&2
    echo "Only PolyFun/Control/Do/, PolyFun/PFunctor/Free/Do.lean, and PolyFunTest/Do/ may" >&2
    echo "depend on it. See AGENTS.md gotcha 8." >&2
    status=1
  fi
done < <(lean_sources)

if grep -rEn --include='*.lean' '@\[expose\][[:space:]]+public section' PolyFun/Interaction; then
  echo "ERROR: Broad exposed public sections are forbidden in PolyFun/Interaction." >&2
  echo "Expose individual definitions, or use 'import all' in proof modules." >&2
  status=1
fi

if (( status != 0 )); then
  exit "$status"
fi

echo "✓ Module scopes and Interaction API boundaries are valid."
