#!/usr/bin/env bash
# Differential harness for the N11 wire anchor (M3 plan D8/D16).
#
# Runs every fixture under fixtures/**/*.sexp AND every worked-example anchor
# under examples/**/*.core.sexp (a *.sexp glob covers both) through BOTH drivers —
# the Haskell production runtime (`cabal run exe:lara -- check`) and the Lean
# executable semantics (`lean/.lake/build/bin/lara-driver`) — and asserts
# byte-exact agreement on stdout AND exit code. The Lean executable is the oracle:
# any disagreement is a bug (in Haskell or in a fixture), never silently
# re-annotated. The worked-example anchors are derived from their `.lara` sources
# by `scripts/gen-worked-examples.hs` (parse → elaborate → encodeUnit).
#
# Usage:  bash scripts/differential.sh
# Exit:   0 iff every fixture agrees; 1 on any disagreement; 2 on a build/setup
#         error or when no fixtures were found (an empty corpus must never be a
#         green pass — it means fixtures/ was moved or renamed).
set -u

repo_root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$repo_root" || exit 2

echo "== building both drivers"
cabal build exe:lara >/dev/null 2>&1 || { echo "FAIL: cabal build exe:lara"; exit 2; }
( cd lean && lake build >/dev/null 2>&1 ) || { echo "FAIL: lake build"; exit 2; }

hs_bin="$(cabal list-bin exe:lara 2>/dev/null)"
lean_bin="lean/.lake/build/bin/lara-driver"
[ -x "$hs_bin" ] || { echo "FAIL: no Haskell driver binary"; exit 2; }
[ -x "$lean_bin" ] || { echo "FAIL: no Lean driver binary at $lean_bin"; exit 2; }

pass=0
fail=0

printf '\n%-45s  %-8s  %s\n' "fixture" "exit" "verdict"
printf -- '---------------------------------------------------------------------------\n'
# Read NUL-free paths one per line (find | sort), and run the loop in the current
# shell (process substitution, not a pipe) so the pass/fail counters survive.
while IFS= read -r f; do
  hs_out="$("$hs_bin" check "$f")"; hs_exit=$?
  lean_out="$("$lean_bin" "$f")"; lean_exit=$?
  if [ "$hs_out" = "$lean_out" ] && [ "$hs_exit" = "$lean_exit" ]; then
    pass=$((pass + 1))
    printf '%-45s  %-8s  %s\n' "$(basename "$f")" "$hs_exit" "$hs_out"
  else
    fail=$((fail + 1))
    printf 'MISMATCH %-36s\n' "$(basename "$f")"
    printf '  haskell (exit %s): %s\n' "$hs_exit" "$hs_out"
    printf '  lean    (exit %s): %s\n' "$lean_exit" "$lean_out"
  fi
done < <(find fixtures examples -name '*.sexp' | sort)

printf -- '---------------------------------------------------------------------------\n'
echo "pass=$pass fail=$fail"
if [ "$((pass + fail))" -eq 0 ]; then
  echo "FAIL: no fixtures compared — fixtures/ or examples/ is empty, missing, or renamed"
  exit 2
fi
[ "$fail" -eq 0 ] && [ "$pass" -gt 0 ]
