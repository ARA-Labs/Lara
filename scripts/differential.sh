#!/usr/bin/env bash
# Differential harness for the N11 wire anchor (M3 plan D8/D16).
#
# Runs every fixture under fixtures/**/*.sexp (excluding the deliberately
# malformed envelopes of fixtures/malformed/), every worked-example anchor
# under examples/**/*.core.sexp (excluding the map anchors named map.core.sexp
# and map.verdict.sexp — see the exclusion note below), every replay-bundle anchor under
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
# Negative half (review C8): every fixtures/malformed/*.sexp is a
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
# check and stay silently green (review).
#
# Mutant suite discovery (review): the generated suite under
# fixtures/mutants/ is discovered from fixtures/mutants/MANIFEST.tsv, never
# by globbing, and each half (verdict mutants, codec mutants) must be
# non-empty on its own — legacy fixtures/malformed anchors can no longer
# satisfy the counters for an absent suite. The manifest and the committed
# *.sexp files must also agree exactly (no missing, no unlisted files).
#
# Stderr pinning (re-review + R9): two rejection classes carry
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
# Nesting bound: a third, GENERATED family. Both readers cap
# S-expression nesting at the same `maxDepth`, and the two cases that straddle
# that bound are built here from the constant each reader declares in source
# rather than committed as ten kilobytes of parentheses. Over the bound the
# located refusal message is byte-compared across drivers (prefix stripped),
# because the category, not just the exit code, is the contract that used to
# differ: the Lean reader had no bound at all. See the section itself for why
# the two constants are compared before the cases run.
#
# Usage:  bash scripts/differential.sh
# Exit:   0 iff every anchor agrees (positive byte-parity AND negative
#         exit-2/empty-stdout AND both nesting-bound cases); 1 on any
#         disagreement; 2 on a build/setup error or when no anchors were found
#         (an empty corpus must never be a green pass — it means fixtures/,
#         examples/, bundles/, or corpus-units/ moved).
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
  # Five FAMILIES are excluded, each because it has its own harness: the
  # deliberately malformed envelopes of fixtures/malformed/ are the negative
  # half below; the generated mutant suite (fixtures/mutants/) is discovered
  # manifest-driven, so an absent or half-written suite fails loudly instead of
  # shrinking the anchor set (review); the source admission fixtures
  # (fixtures/admission/) belong to scripts/admission-differential.sh; the
  # possible-world fixtures (fixtures/pw/) have their own harnesses —
  # fixtures/pw/run/ and its worlds/ go through both pw drivers in
  # scripts/check-pw-conformance.py, which also runs the .lara world-source run
  # files of fixtures/pw/source/, and fixtures/pw/declared.sexp is the Lean
  # pw-example host's fixture, exercised by scripts/check-pw-example.py; run
  # documents and pw-surface documents are not check-input@1 envelopes at all,
  # and the world envelopes they name are checked by each runtime's own checker.
  # check-pw-conformance.py asserts totality over fixtures/pw/**, so a stray file
  # there is a setup failure in that gate rather than a free pass here. And a
  # map's two committed artifacts are a map-check-input@1 parity envelope and a
  # map-verdict@1 composite golden, which scripts/check-map-conformance.sh and
  # test/MapSpec.hs own.
  #
  # Why the exclusions are not the safeguard. This positive half treats "both
  # drivers exit 2 with empty stdout" as agreement, so ANY .sexp under these
  # roots that is not a check-input@1 envelope decode-fails on both drivers and
  # is counted as an agreeing byte-parity anchor. Excluding the map's two
  # filenames fixed the two files that existed and does nothing about the next
  # one to arrive under a third name. So the discovered set is pinned against
  # fixtures/ANCHORS.tsv below, exactly as the mutant half pins itself against
  # its own manifest: a stray unlisted file is a setup failure, never a free
  # pass.
  if ! find "$root" -name '*.sexp' -not -path "$root/malformed/*" -not -path "$root/mutants/*" \
      -not -path "$root/admission/*" -not -path "$root/pw/*" \
      -not -name 'map.core.sexp' -not -name 'map.verdict.sexp' \
      -print >"$root_anchor_list"; then
    echo "FAIL: could not discover anchors under $root"
    exit 2
  fi
  if [ ! -s "$root_anchor_list" ]; then
    echo "FAIL: no *.sexp anchors found under required root: $root"
    exit 2
  fi
done

# ---------------------------------------------------------------------------
# Pin the globbed anchor set against its committed manifest. See the note in
# the discovery loop for why a filename exclusion is not enough.
# ---------------------------------------------------------------------------
anchor_manifest="fixtures/ANCHORS.tsv"
if [ ! -f "$anchor_manifest" ]; then
  echo "FAIL: anchor manifest not found: $anchor_manifest (regenerate with scripts/gen-anchor-manifest.sh)"
  exit 2
fi
anchor_listed="$tmp_dir/anchors.listed"
anchor_discovered="$tmp_dir/anchors.discovered"
if ! grep -v '^#' "$anchor_manifest" | grep -v '^[[:space:]]*$' | LC_ALL=C sort >"$anchor_listed"; then
  echo "FAIL: could not read anchor manifest: $anchor_manifest"
  exit 2
fi
if [ ! -s "$anchor_listed" ]; then
  echo "FAIL: anchor manifest lists no anchors: $anchor_manifest"
  exit 2
fi
if ! cat "$tmp_dir"/anchors.fixtures "$tmp_dir"/anchors.examples   "$tmp_dir"/anchors.bundles "$tmp_dir"/anchors.corpus-units   | LC_ALL=C sort >"$anchor_discovered"; then
  echo "FAIL: could not enumerate discovered anchors"
  exit 2
fi
if ! cmp -s "$anchor_listed" "$anchor_discovered"; then
  echo "FAIL: anchor manifest and discovered *.sexp files disagree (regenerate with scripts/gen-anchor-manifest.sh)"
  echo "  only in manifest:"
  comm -23 "$anchor_listed" "$anchor_discovered" | sed 's/^/    /'
  echo "  only on disk:"
  comm -13 "$anchor_listed" "$anchor_discovered" | sed 's/^/    /'
  exit 2
fi

# ---------------------------------------------------------------------------
# Mutant suite (fixtures/mutants/, T1): manifest-driven
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

# Canonical-order pinning (re-review): the negative anchor
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
# Negative anchors (review C8): every fixtures/malformed/*.sexp is a
# deliberately malformed check-input envelope. BOTH drivers must reject it at
# the codec boundary: exit code 2 AND empty stdout. stderr diagnostics are
# free to differ and are never compared (two exceptions: the canonical-order
# anchor above, and the generated codec mutants' manifest-pinned per-operator
# diagnostics — review).
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
  # an absent other (review).
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

# ---------------------------------------------------------------------------
# The reader's nesting bound: GENERATED, not committed.
#
# Both readers — `Lara.Wire.parseSExprBS` and `Lara.Driver.parseWire` — refuse
# input nested deeper than the `maxDepth` they share, so a pathologically nested
# file is a located codec error (exit 2) on each side rather than a stack
# overflow on either. No committed anchor nests more than 20 levels — measured
# below, not assumed — and one at this depth would be ten kilobytes of
# parentheses, so the two cases are generated here from the bound each reader
# declares in its own source.
#
# The two constants are read out and compared FIRST — not because the cases
# below are blind to a one-sided change (they are not: the bound's value is
# printed inside its own message, so raising one side alone changes either the
# wording or the column, and the byte comparison below goes red either way), but
# because this fails EARLIER and BY NAME instead of as an opaque message
# mismatch, and because it catches the constant being renamed, reformatted or
# deleted outright — which the generated cases genuinely cannot.
#
# Over the bound the located message IS compared, once each driver's own
# program-name prefix is stripped — the depth, the column and the wording are
# the shared reader's contract, and it is precisely the refusal CATEGORY that
# used to differ: previously the Lean reader had no bound, read the over-deep
# form, and refused it one layer later as a malformed envelope, at the same exit
# code. At the bound the two diagnostics are NOT compared — the Haskell driver's
# there prints the rejected tree, which is free to differ — but the bound's own
# message must be absent from both, which is what stops a reader that refuses one
# level too early from satisfying the case. A third case does the same for a wide,
# shallow document, pinning that the counter counts DEPTH and not forms seen.
# ---------------------------------------------------------------------------
printf '\n== reader nesting bound (generated from maxDepth; both drivers must refuse alike)\n'

hs_depth="$(sed -n 's/^maxDepth = \([0-9]\{1,\}\)$/\1/p' src/Lara/Wire.hs)"
lean_depth="$(sed -n 's/^def maxDepth : Nat := \([0-9]\{1,\}\)$/\1/p' lean/Lara/Driver.lean)"
if [ -z "$hs_depth" ] || [ -z "$lean_depth" ]; then
  echo "FAIL: could not read the nesting bound from src/Lara/Wire.hs and lean/Lara/Driver.lean"
  exit 2
fi
if [ "$hs_depth" != "$lean_depth" ]; then
  echo "FAIL: the two readers declare different nesting bounds (haskell $hs_depth, lean $lean_depth)"
  exit 2
fi
printf 'shared nesting bound: %s\n' "$hs_depth"

# ---------------------------------------------------------------------------
# The margin, measured rather than asserted.
#
# `docs/spec.md` §10.1, `src/Lara/Wire.hs` and `lean/Lara/Driver.lean` all say
# the bound sits far above anything committed, and §10.1's sentence is normative
# inside a frozen section. Nothing measured it: every gate reads `maxDepth` out
# of source and none looks at the artifacts. So a depth-25 fixture could land and
# silently falsify a frozen spec sentence. Measure it here — the scan is over
# every committed .sexp/.laramap/.lara tree, all 960 of them, and costs
# milliseconds — and fail above the low-water mark the spec states.
# ---------------------------------------------------------------------------
corpus_depth_ceiling=20
corpus_depth_prog='
BEGIN { maxd = 0; maxf = "-" }
FNR == 1 { d = 0; instr = 0; esc = 0 }
{
  n = length($0); incomment = 0
  for (i = 1; i <= n; i++) {
    c = substr($0, i, 1)
    if (esc) { esc = 0; continue }
    if (instr) {
      if (c == "\\") esc = 1
      else if (c == "\"") instr = 0
      continue
    }
    if (incomment) continue
    if (c == ";") { incomment = 1; continue }
    if (c == "\"") { instr = 1; continue }
    if (c == "(") { d++; if (d > maxd) { maxd = d; maxf = FILENAME } }
    else if (c == ")") d--
  }
}
END { printf "%d %s\n", maxd, maxf }
'
# `-exec … +` may batch, so each batch reports its own maximum and the largest
# wins. `sort -rn` orders on the leading depth field.
# `test` is in the roots even though it holds no anchor: the sentence being
# checked is about every committed tree, and test/fixtures/map/ is where the map
# gate's own envelopes live — an entirely plausible place for a deep artifact.
corpus_depth_line="$(find fixtures examples bundles corpus-units test \
  \( -name '*.sexp' -o -name '*.laramap' -o -name '*.lara' \) \
  -exec awk "$corpus_depth_prog" {} + | LC_ALL=C sort -rn | head -1)"
corpus_depth="${corpus_depth_line%% *}"
corpus_depth_file="${corpus_depth_line#* }"
if [ -z "$corpus_depth" ]; then
  echo "FAIL: could not measure the committed artifacts' nesting depth"
  exit 2
fi
if [ "$corpus_depth" -gt "$corpus_depth_ceiling" ]; then
  echo "FAIL: a committed artifact nests $corpus_depth levels ($corpus_depth_file),"
  echo "  past the $corpus_depth_ceiling-level ceiling that docs/spec.md §10.1,"
  echo "  src/Lara/Wire.hs and lean/Lara/Driver.lean all assert. Raise the ceiling"
  echo "  here and update that sentence in all three, or shallow the artifact."
  exit 2
fi
printf 'deepest committed artifact: %s levels (%s), ceiling %s\n' \
  "$corpus_depth" "$corpus_depth_file" "$corpus_depth_ceiling"

depth_dir="$tmp_dir/depth"
if ! mkdir -p "$depth_dir"; then
  echo "FAIL: could not create $depth_dir"
  exit 2
fi

# n copies of one character, without spawning n processes.
repeat_char() {
  # A loop, not sprintf("%*s", n, ""): mawk's sprintf buffer is a fixed 8192
  # bytes and these cases need more, so the sprintf form aborts the gate under
  # the awk that stock Ubuntu — and CI's `ubuntu-latest` — selects by default.
  awk -v n="$1" -v c="$2" 'BEGIN { while (i++ < n) printf "%s", c }'
}

depth_over="$depth_dir/over-the-bound.sexp"
depth_at="$depth_dir/at-the-bound.sexp"
depth_wide="$depth_dir/wide-not-deep.sexp"
repeat_char "$((hs_depth + 2))" '(' >"$depth_over" || exit 2
{
  repeat_char "$((hs_depth + 1))" '('
  repeat_char "$((hs_depth + 1))" ')'
} >"$depth_at" || exit 2
# A third case, for the counter itself. Both cases above are `(((…)))`, one
# element per list, where nesting depth and total-forms-seen are numerically
# equal — so is every committed anchor, none of which holds more than a couple of
# hundred siblings, two orders of magnitude under the bound. Writing Lean's tail
# recursion as `parseList (depth + 1) p''` rather than `parseList depth p''` (the
# slip the mutual threading invites; Haskell's `where`-bound closure cannot
# express it) would leave both cases above passing while the reader refused a
# wide, shallow
# document — falsifying docs/spec.md §10.1's "it bounds no expressible program".
# This document nests one level and holds maxDepth + 2 siblings: both drivers
# still exit 2, because it is not a check-input@1 envelope, but neither may
# refuse it FOR THE BOUND.
{
  printf '('
  awk -v n="$((hs_depth + 2))" 'BEGIN { while (i++ < n) printf "a " }'
  printf ')'
} >"$depth_wide" || exit 2

depth_pass=0
depth_fail=0
depth_message="maximum S-expression nesting depth exceeded ($hs_depth)"
for depth_case in "over:$depth_over" "at:$depth_at" "wide:$depth_wide"; do
  depth_mode="${depth_case%%:*}"
  f="${depth_case#*:}"
  depth_why=''
  case "$depth_mode" in
    wide) depth_label='depth counter: wide, not deep' ;;
    *) depth_label="depth $depth_mode the bound" ;;
  esac
  case_no=$((case_no + 1))
  hs_stdout="$tmp_dir/$case_no.haskell.stdout"
  hs_stderr="$tmp_dir/$case_no.haskell.stderr"
  lean_stdout="$tmp_dir/$case_no.lean.stdout"
  lean_stderr="$tmp_dir/$case_no.lean.stderr"

  "$hs_bin" check "$f" >"$hs_stdout" 2>"$hs_stderr"
  hs_exit=$?
  "$lean_bin" "$f" >"$lean_stdout" 2>"$lean_stderr"
  lean_exit=$?

  # Over the bound the two located messages must agree byte for byte AND must be
  # the bound's own — agreement alone is satisfied by a pair of readers that both
  # ran off the end of the unclosed parens, and by a pair of empty stderrs. At the
  # bound the message must be absent: the form is inside the bound, so what
  # refuses it is the envelope decoder one layer later.
  reason_matches=1
  if [ "$depth_mode" = "over" ]; then
    sed -e 's/^lara: //' "$hs_stderr" >"$tmp_dir/$case_no.haskell.reason"
    sed -e 's/^lara-driver: //' "$lean_stderr" >"$tmp_dir/$case_no.lean.reason"
    if ! cmp -s "$tmp_dir/$case_no.haskell.reason" "$tmp_dir/$case_no.lean.reason"; then
      reason_matches=0
      depth_why='the two readers refused the over-deep input differently'
    elif ! grep -qF "$depth_message" "$hs_stderr"; then
      reason_matches=0
      depth_why='the two readers agree, but not on the nesting bound'
    fi
  elif grep -qF "$depth_message" "$hs_stderr" || grep -qF "$depth_message" "$lean_stderr"; then
    reason_matches=0
    if [ "$depth_mode" = "wide" ]; then
      depth_why='the nesting bound counts forms seen, not nesting depth'
    else
      depth_why='the nesting bound fired one level too early'
    fi
  fi

  if [ "$hs_exit" -eq 2 ] && [ "$lean_exit" -eq 2 ] \
    && [ ! -s "$hs_stdout" ] && [ ! -s "$lean_stdout" ] && [ "$reason_matches" -eq 1 ]; then
    depth_pass=$((depth_pass + 1))
    printf '%-45s  exit 2, empty stdout\n' "$depth_label"
  else
    depth_fail=$((depth_fail + 1))
    printf 'DEPTH MISMATCH [%s] (expected both exit 2 with empty stdout)\n' "$depth_label"
    # Truncated: the Haskell driver's envelope diagnostic prints the rejected
    # tree, which for the wide case is ten thousand atoms.
    printf '  haskell: exit=%s stdout-bytes=%s reason=%s\n' \
      "$hs_exit" "$(wc -c <"$hs_stdout")" "$(sed -e 's/^lara: //' "$hs_stderr" | head -1 | cut -c1-160)"
    printf '  lean:    exit=%s stdout-bytes=%s reason=%s\n' \
      "$lean_exit" "$(wc -c <"$lean_stdout")" "$(sed -e 's/^lara-driver: //' "$lean_stderr" | head -1 | cut -c1-160)"
    if [ "$reason_matches" -eq 0 ]; then
      printf '  %s\n' "$depth_why"
    fi
  fi
done
echo "depth-bound pass=$depth_pass fail=$depth_fail"

[ "$fail" -eq 0 ] && [ "$neg_fail" -eq 0 ] && [ "$depth_fail" -eq 0 ] \
  && [ "$pass" -gt 0 ] && [ "$neg_pass" -gt 0 ] && [ "$depth_pass" -eq 3 ]
