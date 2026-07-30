#!/usr/bin/env bash
# Differential harness for the N11 wire anchor (M3 plan D8/D16).
#
# Runs every fixture under fixtures/**/*.sexp, every worked-example anchor under
# examples/**/*.core.sexp, and every replay-bundle anchor under
# bundles/**/*.core.sexp (a *.sexp glob covers all three) through BOTH drivers —
# the Haskell production runtime (`cabal run exe:lara -- check`) and the Lean
# executable semantics (`lean/.lake/build/bin/lara-driver`) — and asserts
# byte-exact agreement on stdout AND exit code. The Lean executable is the oracle:
# any disagreement is a bug (in Haskell or in an anchor), never silently
# re-annotated. The worked-example and replay-bundle anchors are derived from
# their `.lara` sources by `scripts/gen-worked-examples.hs` (parse → elaborate →
# encodeUnit).
#
# Usage:  bash scripts/differential.sh
# Exit:   0 iff every anchor agrees; 1 on any disagreement; 2 on a build/setup
#         error or when no anchors were found (an empty corpus must never be a
#         green pass — it means fixtures/, examples/, or bundles/ moved).
set -u

repo_root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$repo_root" || exit 2

tmp_dir="$(mktemp -d "${TMPDIR:-/tmp}/lara-differential.XXXXXX")" || {
  echo "FAIL: could not create temporary directory"
  exit 2
}
cleanup() {
  rm -rf "$tmp_dir"
}
trap cleanup EXIT
trap 'exit 129' HUP
trap 'exit 130' INT
trap 'exit 143' TERM

echo "== building both drivers"
cabal_build_log="$tmp_dir/cabal-build.log"
if ! cabal build exe:lara >"$cabal_build_log" 2>&1; then
  echo "FAIL: cabal build exe:lara"
  cat "$cabal_build_log"
  exit 2
fi
lean_build_log="$tmp_dir/lean-build.log"
if ! ( cd lean && lake build ) >"$lean_build_log" 2>&1; then
  echo "FAIL: lake build"
  cat "$lean_build_log"
  exit 2
fi

hs_bin="$(cabal list-bin exe:lara 2>/dev/null)"
lean_bin="lean/.lake/build/bin/lara-driver"
[ -x "$hs_bin" ] || { echo "FAIL: no Haskell driver binary"; exit 2; }
[ -x "$lean_bin" ] || { echo "FAIL: no Lean driver binary at $lean_bin"; exit 2; }

anchor_list="$tmp_dir/anchors.list"
for root in fixtures examples bundles; do
  if [ ! -d "$root" ]; then
    echo "FAIL: required anchor root is not a directory: $root"
    exit 2
  fi

  root_anchor_list="$tmp_dir/anchors.$root"
  if ! find "$root" -name '*.sexp' -print >"$root_anchor_list"; then
    echo "FAIL: could not discover anchors under $root"
    exit 2
  fi
  if [ ! -s "$root_anchor_list" ]; then
    echo "FAIL: no *.sexp anchors found under required root: $root"
    exit 2
  fi
done

if ! sort \
  "$tmp_dir/anchors.fixtures" \
  "$tmp_dir/anchors.examples" \
  "$tmp_dir/anchors.bundles" >"$anchor_list"; then
  echo "FAIL: could not sort discovered anchors"
  exit 2
fi

pass=0
fail=0
case_no=0

printf '\n%-45s  %-8s  %s\n' "anchor" "exit" "verdict"
printf -- '---------------------------------------------------------------------------\n'
# Anchor paths containing newlines or NUL bytes are unsupported. Feed the
# materialized, checked discovery result to this loop in the current shell so
# setup failures cannot become a false pass and the counters survive.
while IFS= read -r f; do
  case_no=$((case_no + 1))
  hs_stdout="$tmp_dir/$case_no.haskell.stdout"
  hs_stderr="$tmp_dir/$case_no.haskell.stderr"
  lean_stdout="$tmp_dir/$case_no.lean.stdout"
  lean_stderr="$tmp_dir/$case_no.lean.stderr"

  "$hs_bin" check "$f" >"$hs_stdout" 2>"$hs_stderr"
  hs_exit=$?
  "$lean_bin" "$f" >"$lean_stdout" 2>"$lean_stderr"
  lean_exit=$?
  if cmp -s "$hs_stdout" "$lean_stdout"; then
    stdout_matches=1
  else
    stdout_matches=0
  fi

  # Command substitution is safe here: these values are presentation-only.
  # The verdict above compares the unmodified files, including trailing LFs.
  hs_display="$(cat "$hs_stdout")"
  if [ "$stdout_matches" -eq 1 ] && [ "$hs_exit" = "$lean_exit" ]; then
    pass=$((pass + 1))
    printf '%-45s  %-8s  %s\n' "$f" "$hs_exit" "$hs_display"
  else
    fail=$((fail + 1))
    lean_display="$(cat "$lean_stdout")"
    printf 'MISMATCH %s\n' "$f"
    printf '  haskell (exit %s): %s\n' "$hs_exit" "$hs_display"
    printf '  lean    (exit %s): %s\n' "$lean_exit" "$lean_display"

    if [ "$stdout_matches" -eq 0 ]; then
      hs_bytes="$(wc -c <"$hs_stdout")"
      lean_bytes="$(wc -c <"$lean_stdout")"
      printf '  stdout bytes: haskell=%s lean=%s\n' "$hs_bytes" "$lean_bytes"
      printf '  stdout byte diff (offset, haskell octal, lean octal; first 20):\n'
      cmp -l "$hs_stdout" "$lean_stdout" 2>&1 | sed -n '1,20p'
    fi
    if [ -s "$hs_stderr" ]; then
      printf '  haskell stderr:\n'
      cat "$hs_stderr"
      printf '\n'
    fi
    if [ -s "$lean_stderr" ]; then
      printf '  lean stderr:\n'
      cat "$lean_stderr"
      printf '\n'
    fi
  fi
done <"$anchor_list"

printf -- '---------------------------------------------------------------------------\n'
echo "pass=$pass fail=$fail"
if [ "$((pass + fail))" -eq 0 ]; then
  echo "FAIL: no anchors compared — fixtures/, examples/, and bundles/ are empty, missing, or renamed"
  exit 2
fi
[ "$fail" -eq 0 ] && [ "$pass" -gt 0 ]
