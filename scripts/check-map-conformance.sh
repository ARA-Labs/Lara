#!/usr/bin/env bash
# Cross-driver conformance harness for the multi-artifact map (issue #303).
#
# The map's counterpart of scripts/differential.sh, and it exists for the same
# reason: a second implementation is only evidence if it reaches its answer on
# its own. The Haskell driver (`lara check <map.laramap>`) reads a manifest,
# rereads and rechecks every member from disk, qualifies, merges, saturates,
# checks and evaluates. The Lean driver (`lean/.lake/build/bin/lara-map-driver`)
# has no `.lara` parser and no manifest parser, so it is handed the
# `map-check-input@1` PARITY ENVELOPE — the same checked-boundary members, as
# elaborated units — and performs the qualification, the merge, the cross-member
# saturation, `checkUnit` and the grounded evaluation itself. Neither driver
# reads the other's verdict.
#
# Three families of anchor. The map anchors come from TWO roots — the fixture
# tree test/fixtures/map/, and the shipped D3 example examples/agreement-map-multi/
# — because the shipped example is the one a reader runs, and a gate that only
# covers hand-built fixtures would let it drift. The malformed envelopes are a
# fixture-only family and stay under test/fixtures/map/malformed/.
#
#   1. map anchors (<root>/**/map.laramap). For each one:
#        * `lara map-input` derives the envelope; the committed map.core.sexp
#          must equal it BYTE FOR BYTE (the freshness half — a member edited
#          without regenerating turns this red rather than silently comparing
#          two drivers over stale bytes);
#        * `lara check` and `lara-map-driver` must agree on stdout bytes AND
#          exit code. A map that both accept is compared on its full
#          map-verdict@1 bytes; a map both refuse after the checked boundary
#          (a false alignment, a linked unit that does not check) is compared
#          on its empty stdout, its exit code, AND its stderr diagnostic with
#          each driver's own name prefix stripped — because two empty stdouts
#          agree no matter WHY each driver refused, and the reason is the whole
#          content of a refusal.
#      A map that fails BEFORE the checked boundary has no envelope at all —
#      `lara map-input` stops where `lara check` does for every boundary stage
#      — so there is nothing to hand the Lean driver. Such an anchor CONTRIBUTES
#      NO CROSS-DRIVER EVIDENCE, and the summary counts it in its own column
#      rather than in the parity total: "6 anchors" must never be readable as
#      "6 anchors of parity". What it is still checked for is that both Haskell
#      doors refuse the same map for the same STATED reason — equal exit codes
#      drawn from the map door's own refusal set {1, 2}, empty stdout on both,
#      and byte-identical stderr once the `lara: ` prefix is stripped. The weaker
#      earlier test (equal exits, empty stdouts) was satisfied just as well by a
#      binary dying of an uncaught exception at both doors, which is why the
#      reason is compared and the exit code is constrained.
#
#      The run FAILS outright when no anchor reaches the Lean driver, because
#      that is the state in which this script reports agreement having run the
#      second implementation zero times.
#
#   2. malformed envelopes (test/fixtures/map/malformed/*.sexp). Hand-written
#      bytes no frontend would emit. Both DECODERS must refuse each one: the
#      Lean driver at exit 2 with empty stdout, and the Haskell decoder in
#      test/MapSpec.hs (`prop_malformedEnvelopesAreRefused`), which is where the
#      in-process half lives because there is no CLI door that decodes an
#      envelope — `lara check map.laramap` deliberately never reads one.
#
#   3. the generated differential. Families 1 and 2 assert each side separately:
#      one runs both drivers over a handful of well-formed anchors, the other
#      asks each decoder to refuse the same hand-written corpus. Neither runs
#      arbitrary bytes through BOTH decoders and compares the accept/reject
#      DECISION — which is the divergence class the malformed corpus exists to
#      catch, and the one a hand-curated list structurally cannot: a divergence
#      in the middle of the language stays invisible until someone happens to
#      write that fixture. (This PR found its empty-member-path divergence by
#      hand for exactly that reason; fuzzing did not find it either.)
#
#      `map-envelope-differential` mechanically mutates the committed envelopes,
#      decides each mutant with the Haskell decoder, and writes the bytes plus
#      the decision. This loop runs the Lean driver over the same bytes and
#      fails on any disagreement: a mutant the Haskell decoder ACCEPTED must not
#      make the Lean driver exit 2, and one it REFUSED must. The corpus is
#      required to contain both decisions, because a differential over refusals
#      alone is satisfied by two decoders that refuse everything.
#
# Regenerating a committed envelope or verdict, after editing a member or a
# manifest (never by hand):
#
#     cabal build exe:lara
#     "$(cabal list-bin exe:lara)" map-input DIR/map.laramap > DIR/map.core.sexp
#     "$(cabal list-bin exe:lara)" check DIR/map.laramap \
#       > DIR/map.verdict.sexp                     # accepting anchors only
#
# where DIR is the anchor's own directory under either root.
#
# Usage:  bash scripts/check-map-conformance.sh
# Exit:   0 iff every anchor agrees; 1 on any disagreement; 2 on a build/setup
#         error or when either root contributed no anchors (an empty corpus must
#         never be a green pass — it means test/fixtures/map/ or
#         examples/agreement-map-multi/ moved).
set -u

repo_root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$repo_root" || exit 2

tmp_dir="$(mktemp -d "${TMPDIR:-/tmp}/lara-map-conformance.XXXXXX")" || {
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
if ! ( cd lean && lake build lara-map-driver ) >"$lean_build_log" 2>&1; then
  echo "FAIL: lake build lara-map-driver"
  cat "$lean_build_log"
  exit 2
fi

differential_build_log="$tmp_dir/cabal-differential.log"
if ! cabal build exe:map-envelope-differential >"$differential_build_log" 2>&1; then
  echo "FAIL: cabal build exe:map-envelope-differential"
  cat "$differential_build_log"
  exit 2
fi

hs_bin="$(cabal list-bin exe:lara 2>/dev/null)"
diff_bin="$(cabal list-bin exe:map-envelope-differential 2>/dev/null)"
lean_bin="lean/.lake/build/bin/lara-map-driver"
[ -x "$hs_bin" ] || { echo "FAIL: no Haskell driver binary"; exit 2; }
[ -x "$lean_bin" ] || { echo "FAIL: no Lean map driver binary at $lean_bin"; exit 2; }
[ -x "$diff_bin" ] || { echo "FAIL: no differential generator binary"; exit 2; }

map_root="test/fixtures/map"
[ -d "$map_root" ] || { echo "FAIL: no map fixture root at $map_root"; exit 2; }

# Each root is required to contribute at least one anchor ON ITS OWN, so a
# renamed or emptied root cannot hide behind the other one's anchors.
anchor_list="$tmp_dir/anchors.list"
: >"$anchor_list"
for anchor_root in "$map_root" examples/agreement-map-multi; do
  if [ ! -d "$anchor_root" ]; then
    echo "FAIL: required map anchor root is not a directory: $anchor_root"
    exit 2
  fi
  root_anchor_list="$tmp_dir/anchors.root"
  if ! find "$anchor_root" -name 'map.laramap' -print | sort >"$root_anchor_list"; then
    echo "FAIL: could not discover map anchors under $anchor_root"
    exit 2
  fi
  if [ ! -s "$root_anchor_list" ]; then
    echo "FAIL: no map.laramap anchors found under $anchor_root"
    exit 2
  fi
  cat "$root_anchor_list" >>"$anchor_list"
done

malformed_list="$tmp_dir/malformed.list"
if ! find "$map_root/malformed" -name '*.sexp' -print | sort >"$malformed_list"; then
  echo "FAIL: could not discover malformed envelopes under $map_root/malformed"
  exit 2
fi
if [ ! -s "$malformed_list" ]; then
  echo "FAIL: no malformed envelopes found under $map_root/malformed"
  exit 2
fi

# `pass` counts only anchors that REACHED the Lean driver, so it is the size of
# the cross-driver evidence and nothing else. `preboundary` counts anchors that
# stopped at a Haskell-side boundary and therefore produced no envelope to hand
# over; they are checked (both doors, same reason) but they are not parity.
pass=0
preboundary=0
fail=0
case_no=0

printf '\n%-42s  %-6s  %s\n' "anchor" "exit" "outcome"
printf -- '---------------------------------------------------------------------------\n'
while IFS= read -r manifest; do
  case_no=$((case_no + 1))
  dir="$(dirname "$manifest")"
  hs_stdout="$tmp_dir/$case_no.haskell.stdout"
  hs_stderr="$tmp_dir/$case_no.haskell.stderr"
  lean_stdout="$tmp_dir/$case_no.lean.stdout"
  lean_stderr="$tmp_dir/$case_no.lean.stderr"
  envelope="$tmp_dir/$case_no.envelope.sexp"
  mi_stderr="$tmp_dir/$case_no.mapinput.stderr"

  "$hs_bin" check "$manifest" >"$hs_stdout" 2>"$hs_stderr"
  hs_exit=$?
  "$hs_bin" map-input "$manifest" >"$envelope" 2>"$mi_stderr"
  mi_exit=$?

  if [ "$mi_exit" -ne 0 ]; then
    # A boundary failure: the map never reached the checked boundary, so no
    # envelope exists for the Lean driver to be given. This anchor therefore
    # contributes NOTHING to the cross-driver total, and is counted separately
    # (see `preboundary` below) so that "6 anchors" can never be read as "6
    # anchors of parity evidence".
    #
    # What is still comparable is that the two Haskell doors refuse the same map
    # for the same stated reason. An earlier version of this branch checked only
    # that both exits were equal and both stdouts empty, which a driver that
    # dies of an uncaught exception at both doors satisfies exactly as well as a
    # legitimate boundary refusal does. So require, in addition:
    #
    #   * the exit code is a REFUSAL the map door defines — 1 (a map rejection)
    #     or 2 (a boundary/codec failure) — and not 130, 139, or anything else a
    #     crash or a signal produces;
    #   * `map-input` printed a diagnostic at all (an empty stderr means nothing
    #     was explained, which no refusal path here is allowed to do); and
    #   * the two diagnostics are byte-identical once each door's own `lara: `
    #     prefix is stripped, so the two doors are shown to stop for the same
    #     reason rather than merely to stop.
    preboundary_ok=1
    case "$hs_exit" in
      1|2) ;;
      *) preboundary_ok=0 ;;
    esac
    [ "$mi_exit" = "$hs_exit" ] || preboundary_ok=0
    [ ! -s "$hs_stdout" ] || preboundary_ok=0
    [ ! -s "$envelope" ] || preboundary_ok=0
    [ -s "$mi_stderr" ] || preboundary_ok=0
    [ -s "$hs_stderr" ] || preboundary_ok=0
    if [ "$preboundary_ok" -eq 1 ]; then
      hs_reason="$tmp_dir/$case_no.haskell.reason"
      mi_reason="$tmp_dir/$case_no.mapinput.reason"
      sed -e 's/^lara: //' "$hs_stderr" >"$hs_reason"
      sed -e 's/^lara: //' "$mi_stderr" >"$mi_reason"
      cmp -s "$hs_reason" "$mi_reason" || preboundary_ok=0
    fi

    if [ "$preboundary_ok" -eq 1 ]; then
      preboundary=$((preboundary + 1))
      printf '%-42s  %-6s  %s\n' "$manifest" "$hs_exit" "pre-boundary (no envelope; no parity evidence)"
    else
      fail=$((fail + 1))
      printf 'MISMATCH %s\n' "$manifest"
      printf '  lara check     exit %s, %s stdout bytes\n' "$hs_exit" "$(wc -c <"$hs_stdout")"
      printf '  lara map-input exit %s, %s stdout bytes\n' "$mi_exit" "$(wc -c <"$envelope")"
      printf '  lara check     reason: %s\n' "$(sed -e 's/^lara: //' "$hs_stderr")"
      printf '  lara map-input reason: %s\n' "$(sed -e 's/^lara: //' "$mi_stderr")"
    fi
    continue
  fi

  committed="$dir/map.core.sexp"
  if [ ! -f "$committed" ]; then
    fail=$((fail + 1))
    printf 'MISMATCH %s\n' "$manifest"
    printf '  no committed envelope at %s (regenerate: see this script header)\n' "$committed"
    continue
  fi
  if ! cmp -s "$committed" "$envelope"; then
    fail=$((fail + 1))
    printf 'STALE %s\n' "$committed"
    printf '  the committed envelope is not what lara map-input derives today\n'
    printf '  (regenerate: see this script header)\n'
    continue
  fi

  "$lean_bin" "$committed" >"$lean_stdout" 2>"$lean_stderr"
  lean_exit=$?

  # A REFUSED map prints no verdict, so stdout is empty on both sides and
  # comparing it is `0 bytes == 0 bytes` — which would pass just as happily if
  # Lean refused for a different reason than Haskell did (a link rejection where
  # Haskell found a false alignment, say). The diagnostic is the only place that
  # distinction is visible, and `Lara.Map.Driver.rejectMessage` claims to mirror
  # `Lara.Map.Types.renderMapError` word for word after each driver's own name.
  # So for a refusal, byte-compare stderr with that one prefix stripped, and
  # require it non-empty. This is the same treatment scripts/differential.sh
  # gives its two stderr-pinned rejection classes, and for the same reason: the
  # stdout comparison cannot isolate which check fired.
  stderr_matches=1
  if [ "$hs_exit" != "0" ]; then
    hs_reason="$tmp_dir/$case_no.haskell.reason"
    lean_reason="$tmp_dir/$case_no.lean.reason"
    sed -e 's/^lara: //' "$hs_stderr" >"$hs_reason"
    sed -e 's/^lara-map-driver: //' "$lean_stderr" >"$lean_reason"
    if ! cmp -s "$hs_reason" "$lean_reason" || [ ! -s "$hs_reason" ]; then
      stderr_matches=0
    fi
  fi

  if cmp -s "$hs_stdout" "$lean_stdout" && [ "$hs_exit" = "$lean_exit" ] \
      && [ "$stderr_matches" -eq 1 ]; then
    pass=$((pass + 1))
    if [ "$hs_exit" = "0" ]; then
      outcome="verdicts agree ($(wc -c <"$hs_stdout") bytes)"
    else
      outcome="both refuse, same reason, no verdict"
    fi
    printf '%-42s  %-6s  %s\n' "$manifest" "$hs_exit" "$outcome"
  else
    fail=$((fail + 1))
    printf 'MISMATCH %s\n' "$manifest"
    printf '  haskell (exit %s): %s\n' "$hs_exit" "$(cat "$hs_stdout")"
    printf '  lean    (exit %s): %s\n' "$lean_exit" "$(cat "$lean_stdout")"
    if [ "$stderr_matches" -eq 0 ]; then
      printf '  haskell reason: %s\n' "$(sed -e 's/^lara: //' "$hs_stderr")"
      printf '  lean    reason: %s\n' "$(sed -e 's/^lara-map-driver: //' "$lean_stderr")"
    fi
  fi
done <"$anchor_list"

# ---------------------------------------------------------------------------
# Malformed envelopes: the Lean decoder must refuse each one at exit 2 with an
# empty stdout. The Haskell decoder's half of this matrix is in test/MapSpec.hs.
# ---------------------------------------------------------------------------
negative_pass=0
negative_fail=0
printf '\n== malformed envelopes (Lean decoder must refuse each at exit 2)\n'
while IFS= read -r f; do
  case_no=$((case_no + 1))
  out="$tmp_dir/$case_no.negative.stdout"
  "$lean_bin" "$f" >"$out" 2>/dev/null
  code=$?
  if [ "$code" = "2" ] && [ ! -s "$out" ]; then
    negative_pass=$((negative_pass + 1))
  else
    negative_fail=$((negative_fail + 1))
    printf 'NEGATIVE MISMATCH %s: exit %s, %s stdout bytes (want exit 2, 0 bytes)\n' \
      "$f" "$code" "$(wc -c <"$out")"
  fi
done <"$malformed_list"
printf 'negative pass=%s fail=%s\n' "$negative_pass" "$negative_fail"

# ---------------------------------------------------------------------------
# Generated differential: the same bytes through BOTH decoders, decisions
# compared. See family 3 in the header.
# ---------------------------------------------------------------------------
printf '\n== generated differential (both decoders must agree on accept/reject)\n'
diff_dir="$tmp_dir/differential"
diff_log="$tmp_dir/differential.log"
# Only the anchors that HAVE a committed envelope: a pre-boundary anchor never
# reaches the checked boundary, so there is nothing for either decoder to read.
diff_inputs=""
while IFS= read -r manifest; do
  candidate="$(dirname "$manifest")/map.core.sexp"
  [ -f "$candidate" ] && diff_inputs="$diff_inputs $candidate"
done <"$anchor_list"
if [ -z "$diff_inputs" ]; then
  echo "FAIL: no committed envelope to derive a differential corpus from"
  exit 2
fi
if ! "$diff_bin" "$diff_dir" $diff_inputs >"$diff_log" 2>&1; then
  echo "FAIL: could not generate the differential corpus"
  cat "$diff_log"
  exit 2
fi
cat "$diff_log"

differential_pass=0
differential_fail=0
while IFS="$(printf '\t')" read -r case_file expected label; do
  [ -n "$case_file" ] || continue
  "$lean_bin" "$diff_dir/$case_file" >"$tmp_dir/differential.stdout" 2>/dev/null
  lean_code=$?
  case "$expected" in
    reject) lean_decision=$([ "$lean_code" = "2" ] && echo reject || echo accept) ;;
    accept) lean_decision=$([ "$lean_code" = "0" ] || [ "$lean_code" = "1" ] && echo accept || echo reject) ;;
    *) echo "FAIL: unreadable decision '$expected' for $case_file"; exit 2 ;;
  esac
  if [ "$lean_decision" = "$expected" ]; then
    differential_pass=$((differential_pass + 1))
  else
    differential_fail=$((differential_fail + 1))
    printf 'DIFFERENTIAL MISMATCH %s (%s)\n' "$case_file" "$label"
    printf '  haskell decoder: %s\n' "$expected"
    printf '  lean driver:     %s (exit %s)\n' "$lean_decision" "$lean_code"
    printf '  bytes:           %s\n' "$diff_dir/$case_file"
  fi
done <"$diff_dir/decisions.tsv"
printf 'differential pass=%s fail=%s\n' "$differential_pass" "$differential_fail"

printf '\nmap anchors: cross-driver pass=%s  pre-boundary=%s  fail=%s\n' \
  "$pass" "$preboundary" "$fail"

# An all-pre-boundary run is the failure this gate exists to prevent: every
# anchor refused before the boundary means the Lean driver ran ZERO times, and
# the run below would otherwise print "both drivers agree" having compared no
# driver against any other. A Haskell binary that crashes identically at both
# doors reaches exactly this state.
if [ "$pass" -eq 0 ]; then
  printf 'FAIL: no anchor reached the Lean driver; there is no cross-driver evidence\n'
  printf '      (%s anchors stopped pre-boundary; the Lean driver ran 0 times)\n' "$preboundary"
  exit 1
fi

if [ "$fail" -eq 0 ] && [ "$negative_fail" -eq 0 ] && [ "$differential_fail" -eq 0 ]; then
  printf 'OK: both drivers agree on all %s anchors that reached the boundary' "$pass"
  if [ "$preboundary" -gt 0 ]; then
    printf ' (%s more refused pre-boundary, no envelope to compare)' "$preboundary"
  fi
  printf '\n'
  exit 0
fi
exit 1
