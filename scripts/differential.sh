#!/usr/bin/env bash
# Differential harness for the N11 wire anchor (M3 plan D8/D16).
#
# Runs every fixture under fixtures/**/*.sexp (excluding the deliberately
# malformed envelopes of fixtures/malformed/), every worked-example anchor
# under examples/**/*.core.sexp, every replay-bundle anchor under
# bundles/**/*.core.sexp, and every T2 corpus-unit anchor under
# corpus-units/**/unit.core.sexp (a *.sexp glob covers all four; the
# corpus-unit set itself is pinned manifest-exact by test/CorpusUnitsSpec.hs,
# so the glob here cannot silently shrink it) through BOTH drivers —
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
# diagnostics are free to differ and are never compared — with TWO
# exceptions: the canonical-order anchor below also pins a per-driver stderr
# substring, because exit-2-only cannot isolate which check fired there; and
# every generated codec mutant (fixtures/mutants/malformed/) pins the
# per-operator stderr substrings recorded in the mutant manifest's
# hs-diagnostic / lean-diagnostic columns, for the same reason — with a codec
# check deleted, its mutants would still exit 2 via a different downstream
# check and stay silently green (PR #49 review).
#
# Mutant suite discovery (PR #49 review): the generated suite under
# fixtures/mutants/ is discovered from fixtures/mutants/MANIFEST.tsv, never
# by globbing, and each half (verdict mutants, codec mutants) must be
# non-empty on its own — legacy fixtures/malformed anchors can no longer
# satisfy the counters for an absent suite. The manifest and the committed
# *.sexp files must also agree exactly (no missing, no unlisted files).
#
# Stderr pinning (PR #44 re-review + #45 R9): two rejection classes carry
# their location only on stderr, because the stdout verdict is a bare class
# atom. The three fixtures/corpus/reject-preflight-*.sexp anchors all emit
# "(verdict … reject R13)", so the duplicate → unknown → unselected-certificate
# precedence is observable only via the replayFailureMessage line; the
# fixtures/corpus/reject-r9.sexp anchor emits "(verdict … reject R9)", which
# cannot say which group conflicted — the groupConflictMessage line does. Both
# template families are byte-identical across drivers by construction, so for
# these anchors the harness additionally byte-compares stderr — a Lean-side
# regression turns red here instead of passing silently.
#
# Usage:  bash scripts/differential.sh
# Exit:   0 iff every anchor agrees (positive byte-parity AND negative
#         exit-2/empty-stdout); 1 on any disagreement; 2 on a build/setup
#         error or when no anchors were found (an empty corpus must never be a
#         green pass — it means fixtures/, examples/, bundles/, or
#         corpus-units/ moved).
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
for root in fixtures examples bundles corpus-units; do
  if [ ! -d "$root" ]; then
    echo "FAIL: required anchor root is not a directory: $root"
    exit 2
  fi

  root_anchor_list="$tmp_dir/anchors.$root"
  # The deliberately malformed envelopes of fixtures/malformed/ are the
  # negative half below, not byte-parity anchors. The whole generated mutant
  # suite (fixtures/mutants/) is excluded from globbing entirely: it is
  # discovered manifest-driven below, so an absent or half-written suite
  # fails loudly instead of shrinking the anchor set (PR #49 review).
  if ! find "$root" -name '*.sexp' -not -path "$root/malformed/*" -not -path "$root/mutants/*" -print >"$root_anchor_list"; then
    echo "FAIL: could not discover anchors under $root"
    exit 2
  fi
  if [ ! -s "$root_anchor_list" ]; then
    echo "FAIL: no *.sexp anchors found under required root: $root"
    exit 2
  fi
done

# ---------------------------------------------------------------------------
# Mutant suite (fixtures/mutants/, M5 tracker #48 T1): manifest-driven
# discovery. The manifest is the source of truth: split its rows into the
# verdict half (byte-parity anchors) and the codec half (negative anchors),
# require EACH half non-empty, and require the committed *.sexp files to
# match the manifest exactly — a missing suite, a stale manifest, or an
# unlisted stray file is a setup failure, never a silent pass.
# ---------------------------------------------------------------------------
mutant_root="fixtures/mutants"
mutant_manifest="$mutant_root/MANIFEST.tsv"
if [ ! -f "$mutant_manifest" ]; then
  echo "FAIL: mutant manifest not found: $mutant_manifest (regenerate with scripts/gen-mutants.hs)"
  exit 2
fi

mutant_positive_rel="$tmp_dir/mutants.positive.rel"
mutant_codec_rel="$tmp_dir/mutants.codec.rel"
if ! awk -F'\t' '!/^#/ && NF >= 5 && $5 == "codec-reject" {print $1}' "$mutant_manifest" >"$mutant_codec_rel" ||
  ! awk -F'\t' '!/^#/ && NF >= 5 && $5 != "codec-reject" {print $1}' "$mutant_manifest" >"$mutant_positive_rel"; then
  echo "FAIL: could not parse mutant manifest: $mutant_manifest"
  exit 2
fi
if [ ! -s "$mutant_positive_rel" ]; then
  echo "FAIL: mutant manifest lists no verdict mutants: $mutant_manifest"
  exit 2
fi
if [ ! -s "$mutant_codec_rel" ]; then
  echo "FAIL: mutant manifest lists no codec mutants: $mutant_manifest"
  exit 2
fi

mutant_listed="$tmp_dir/mutants.listed"
mutant_committed="$tmp_dir/mutants.committed"
if ! sed "s|^|$mutant_root/|" "$mutant_positive_rel" "$mutant_codec_rel" | sort >"$mutant_listed" ||
  ! find "$mutant_root" -name '*.sexp' -print | sort >"$mutant_committed"; then
  echo "FAIL: could not enumerate mutant suite files under $mutant_root"
  exit 2
fi
if ! cmp -s "$mutant_listed" "$mutant_committed"; then
  echo "FAIL: mutant manifest and committed *.sexp files disagree (regenerate with scripts/gen-mutants.hs)"
  echo "  only in manifest:"
  comm -23 "$mutant_listed" "$mutant_committed" | sed 's/^/    /'
  echo "  only on disk:"
  comm -13 "$mutant_listed" "$mutant_committed" | sed 's/^/    /'
  exit 2
fi

mutant_positive_list="$tmp_dir/mutants.positive"
sed "s|^|$mutant_root/|" "$mutant_positive_rel" >"$mutant_positive_list"

if ! sort \
  "$tmp_dir/anchors.fixtures" \
  "$tmp_dir/anchors.examples" \
  "$tmp_dir/anchors.bundles" \
  "$tmp_dir/anchors.corpus-units" \
  "$mutant_positive_list" >"$anchor_list"; then
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

  # Stderr-pinned anchors. Two rejection classes carry their location only on
  # stderr because the stdout verdict is a bare class atom:
  #   * reject-preflight-* (R13): all three ReplayFailure kinds collapse to the
  #     identical "reject R13", so the duplicate → unknown → unselected-cert
  #     precedence is observable only via the replayFailureMessage line;
  #   * reject-r9 (R9): the escalated group-conflict verdict "reject R9" cannot
  #     say which group conflicted — the groupConflictMessage line does.
  # Both templates are byte-identical across drivers, so byte-compare stderr for
  # these anchors (and require it non-empty); every other anchor's stderr stays
  # free.
  stderr_matches=1
  case "$f" in
    fixtures/corpus/reject-preflight-*.sexp | fixtures/corpus/reject-r9.sexp)
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
  echo "FAIL: no anchors compared — fixtures/, examples/, bundles/, or corpus-units/ are empty, missing, or renamed"
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
# free to differ and are never compared (two exceptions: the canonical-order
# anchor above, and the generated codec mutants' manifest-pinned per-operator
# diagnostics — PR #49 review).
# ---------------------------------------------------------------------------
printf '\n== negative anchors (fixtures/malformed + manifest codec mutants): both drivers must exit 2 with empty stdout\n'

if [ ! -d "fixtures/malformed" ]; then
  echo "FAIL: required negative-anchor root is not a directory: fixtures/malformed"
  exit 2
fi

# The legacy hand-written negatives are discovered by glob and must be
# non-empty ON THEIR OWN; the generated codec mutants come from the manifest
# codec half validated above (also non-empty on its own). Merging happens
# only after both counters are satisfied, so neither half can stand in for
# an absent other (PR #49 review).
legacy_negative_list="$tmp_dir/negative.legacy"
if ! find fixtures/malformed -name '*.sexp' -print >"$legacy_negative_list"; then
  echo "FAIL: could not discover negative anchors under fixtures/malformed"
  exit 2
fi
if [ ! -s "$legacy_negative_list" ]; then
  echo "FAIL: no *.sexp negative anchors found under fixtures/malformed"
  exit 2
fi

mutant_codec_list="$tmp_dir/mutants.codec"
sed "s|^|$mutant_root/|" "$mutant_codec_rel" >"$mutant_codec_list"

negative_list="$tmp_dir/negative.list"
if ! sort "$legacy_negative_list" "$mutant_codec_list" >"$negative_list"; then
  echo "FAIL: could not sort discovered negative anchors"
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

  # Diagnostic pins (see header): exit-2-only cannot isolate WHICH codec
  # check fired, so two anchor families additionally pin per-driver stderr
  # substrings:
  #   * the canonical-order anchor: the canonical-order check — not the
  #     list-ordered theory-identity check — must be the rejection that fired;
  #   * every generated codec mutant: the operator's intended check must be
  #     the one that fired, via the hs-diagnostic / lean-diagnostic columns
  #     of the mutant manifest (empty pins are a manifest bug and fail).
  diag_matches=1
  hs_pin=''
  lean_pin=''
  case "$f" in
    fixtures/malformed/non-canonical-theory-order.sexp)
      hs_pin='not in strictly increasing Unicode-scalar order'
      lean_pin='theories must be strictly sorted'
      ;;
    "$mutant_root"/malformed/*.sexp)
      rel="${f#"$mutant_root"/}"
      hs_pin="$(awk -F'\t' -v p="$rel" '!/^#/ && $1 == p {print $6; exit}' "$mutant_manifest")"
      lean_pin="$(awk -F'\t' -v p="$rel" '!/^#/ && $1 == p {print $7; exit}' "$mutant_manifest")"
      if [ -z "$hs_pin" ] || [ -z "$lean_pin" ]; then
        diag_matches=0
      fi
      ;;
  esac
  if [ "$diag_matches" -eq 1 ] && [ -n "$hs_pin" ]; then
    if ! grep -qF "$hs_pin" "$hs_stderr" || ! grep -qF "$lean_pin" "$lean_stderr"; then
      diag_matches=0
    fi
  fi

  if [ "$hs_exit" -eq 2 ] && [ "$lean_exit" -eq 2 ] && [ ! -s "$hs_stdout" ] && [ ! -s "$lean_stdout" ] && [ "$diag_matches" -eq 1 ]; then
    neg_pass=$((neg_pass + 1))
    printf '%-45s  exit 2, empty stdout\n' "$f"
  else
    neg_fail=$((neg_fail + 1))
    printf 'NEGATIVE MISMATCH %s (expected both exit 2 with empty stdout)\n' "$f"
    printf '  haskell: exit=%s stdout-bytes=%s\n' "$hs_exit" "$(wc -c <"$hs_stdout")"
    printf '  lean:    exit=%s stdout-bytes=%s\n' "$lean_exit" "$(wc -c <"$lean_stdout")"
    if [ "$diag_matches" -eq 0 ]; then
      printf '  stderr pin failed: the intended codec check did not fire on at least one driver\n'
      printf '  (expected haskell stderr to contain "%s",\n' "$hs_pin"
      printf '   lean stderr to contain "%s")\n' "$lean_pin"
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
