#!/usr/bin/env bash
# Differential harness for the N11 wire anchor (M3 plan D8/D16).
#
# Runs every fixture under fixtures/**/*.sexp (excluding the deliberately
# malformed envelopes of fixtures/malformed/), every worked-example anchor
# under examples/**/*.core.sexp, and every replay-bundle anchor under
# bundles/**/*.core.sexp (a *.sexp glob covers all three) through BOTH drivers —
# the Haskell production runtime (`cabal run exe:lara -- check`) and the Lean
# executable semantics (`lean/.lake/build/bin/lara-driver`) — and asserts
# byte-exact agreement on stdout AND exit code. The Lean executable is the oracle:
# any disagreement is a bug (in Haskell or in an anchor), never silently
# re-annotated. The worked-example and replay-bundle anchors are derived from
# their `.lara` sources by `scripts/gen-worked-examples.hs` (parse → elaborate →
# encodeUnit).
#
# Negative half (PR #44 review C8): every fixtures/malformed/*.sexp is a
# deliberately malformed check-input envelope. Both drivers must reject each
# one at the codec boundary — exit code 2 with empty stdout — reported as
# "negative pass=N fail=M" and folded into the exit status. stderr
# diagnostics are free to differ and are never compared — with ONE
# exception: the canonical-order anchor below also pins a per-driver stderr
# substring, because exit-2-only cannot isolate which check fired there.
#
# Preflight precedence pinning (PR #44 re-review): the three
# fixtures/corpus/reject-preflight-*.sexp anchors all emit the identical
# stdout verdict "(verdict … reject R13)", so the duplicate → unknown →
# unselected-certificate precedence is observable only on stderr. The
# replayFailureMessage templates are byte-identical across drivers by
# construction, so for these three anchors the harness additionally
# byte-compares stderr — a Lean-side precedence regression turns red here
# instead of passing silently.
#
# Usage:  bash scripts/differential.sh
# Exit:   0 iff every anchor agrees (positive byte-parity AND negative
#         exit-2/empty-stdout); 1 on any disagreement; 2 on a build/setup
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
  # The deliberately malformed envelopes of fixtures/malformed/ are the
  # negative half below, not byte-parity anchors: exclude them here.
  if ! find "$root" -name '*.sexp' -not -path "$root/malformed/*" -print >"$root_anchor_list"; then
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

  # Preflight precedence anchors (PR #44 re-review): all three ReplayFailure
  # kinds collapse to the identical stdout verdict "reject R13", so the
  # duplicate → unknown → unselected-certificate precedence is observable
  # only via the stderr replayFailureMessage line. Those templates are
  # byte-identical across drivers, so byte-compare stderr for these anchors
  # (and require it non-empty); every other anchor's stderr stays free.
  stderr_matches=1
  case "$f" in
    fixtures/corpus/reject-preflight-*.sexp)
      if ! cmp -s "$hs_stderr" "$lean_stderr" || [ ! -s "$hs_stderr" ]; then
        stderr_matches=0
      fi
      ;;
  esac

  # Command substitution is safe here: these values are presentation-only.
  # The verdict above compares the unmodified files, including trailing LFs.
  hs_display="$(cat "$hs_stdout")"
  if [ "$stdout_matches" -eq 1 ] && [ "$hs_exit" = "$lean_exit" ] && [ "$stderr_matches" -eq 1 ]; then
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
    if [ "$stderr_matches" -eq 0 ]; then
      printf '  stderr mismatch on a preflight-precedence anchor (replayFailureMessage must be byte-identical)\n'
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

# Canonical-order pinning (issue #36 re-review): the negative anchor
# fixtures/malformed/non-canonical-theory-order.sexp cannot isolate the
# canonical-order rejection by exit code alone. The theory-identity
# comparison is list-ordered on BOTH drivers (Haskell:
# canonicalUnitTheories /= replayTheories; Lean: sortCodePointStrings keys
# == rid.theories), so with the canonical-order check deleted the envelope
# would STILL exit 2 via TheoryIdentityMismatch and the anchor would stay
# green. For this one anchor the harness therefore additionally greps each
# driver's stderr for its canonical-order diagnostic (the spellings differ
# per driver; codec-boundary diagnostics are not byte-identical the way
# replayFailureMessage is). Every other negative anchor's stderr stays free.
#
# ---------------------------------------------------------------------------
# Negative anchors (PR #44 review C8): every fixtures/malformed/*.sexp is a
# deliberately malformed check-input envelope. BOTH drivers must reject it at
# the codec boundary: exit code 2 AND empty stdout. stderr diagnostics are
# free to differ and are never compared (one exception: the canonical-order
# anchor above).
# ---------------------------------------------------------------------------
printf '\n== negative anchors (fixtures/malformed): both drivers must exit 2 with empty stdout\n'

if [ ! -d fixtures/malformed ]; then
  echo "FAIL: required negative-anchor root is not a directory: fixtures/malformed"
  exit 2
fi

negative_list="$tmp_dir/negative.list"
if ! find fixtures/malformed -name '*.sexp' -print >"$negative_list.unsorted"; then
  echo "FAIL: could not discover negative anchors under fixtures/malformed"
  exit 2
fi
if ! sort "$negative_list.unsorted" >"$negative_list"; then
  echo "FAIL: could not sort discovered negative anchors"
  exit 2
fi
if [ ! -s "$negative_list" ]; then
  echo "FAIL: no *.sexp negative anchors found under fixtures/malformed"
  exit 2
fi

neg_pass=0
neg_fail=0
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

  # Canonical-order pin (see header): for this anchor, require that the
  # canonical-order check — not the list-ordered theory-identity check — is
  # the rejection that fired, on EACH driver, via a fixed substring of its
  # codec diagnostic.
  diag_matches=1
  case "$f" in
    fixtures/malformed/non-canonical-theory-order.sexp)
      if ! grep -qF 'not in strictly increasing Unicode-scalar order' "$hs_stderr" ||
        ! grep -qF 'theories must be strictly sorted' "$lean_stderr"; then
        diag_matches=0
      fi
      ;;
  esac

  if [ "$hs_exit" -eq 2 ] && [ "$lean_exit" -eq 2 ] && [ ! -s "$hs_stdout" ] && [ ! -s "$lean_stdout" ] && [ "$diag_matches" -eq 1 ]; then
    neg_pass=$((neg_pass + 1))
    printf '%-45s  exit 2, empty stdout\n' "$f"
  else
    neg_fail=$((neg_fail + 1))
    printf 'NEGATIVE MISMATCH %s (expected both exit 2 with empty stdout)\n' "$f"
    printf '  haskell: exit=%s stdout-bytes=%s\n' "$hs_exit" "$(wc -c <"$hs_stdout")"
    printf '  lean:    exit=%s stdout-bytes=%s\n' "$lean_exit" "$(wc -c <"$lean_stdout")"
    if [ "$diag_matches" -eq 0 ]; then
      printf '  stderr pin failed: the canonical-order check did not fire on at least one driver\n'
      printf '  (expected haskell stderr to contain "not in strictly increasing Unicode-scalar order",\n'
      printf '   lean stderr to contain "theories must be strictly sorted")\n'
    fi
    if [ -s "$hs_stdout" ]; then
      printf '  haskell stdout: %s\n' "$(cat "$hs_stdout")"
    fi
    if [ -s "$lean_stdout" ]; then
      printf '  lean stdout: %s\n' "$(cat "$lean_stdout")"
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
done <"$negative_list"

echo "negative pass=$neg_pass fail=$neg_fail"
[ "$fail" -eq 0 ] && [ "$neg_fail" -eq 0 ] && [ "$pass" -gt 0 ] && [ "$neg_pass" -gt 0 ]
