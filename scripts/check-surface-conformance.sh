#!/usr/bin/env bash
set -euo pipefail

# Cross-language surface-conformance contract.
#
# MANIFEST.tsv is ordered and has exactly five columns.  `features` is a
# comma-separated set drawn from the closed vocabulary below; every token is
# required to occur.  The canonical output has exactly this header:
#
# case_id  ast_fingerprint  outcome  core_fingerprint  obligations  attacks  observations
#
# Fingerprints are 16 lowercase hexadecimal digits: FNV-1a-64 over the UTF-8
# bytes of a length-framed structured encoding.  List cells are `-` when empty;
# otherwise they are source-order comma-separated percent-escaped UTF-8 atoms.
# Observations use grounded,complete,preferred,stable,semi-stable order and
# spell results gap|justified|contested|defeated|noExtension.  Outcome is
# `accept` or `reject:<stable-structural-tag>`.  No cross-language `Show`/`Repr`
# text is part of this contract.

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
manifest="$repo_root/fixtures/surface/MANIFEST.tsv"
golden="${SURFACE_CONFORMANCE_GOLDEN:-$repo_root/test/surface-conformance.golden}"
mode=check

case "${1:-}" in
  "") ;;
  --update) mode=update ;;
  *) echo "surface conformance: FAIL: usage: $0 [--update]" >&2; exit 2 ;;
esac

required_features=(
  labelled-premise named-discharge comparison value-interpolation
  cell-interpolation named-cert-premise named-formula rule-binder nd-binder
  surface-attacks capture-rejection ambiguous-premise-rejection
  comparison-polarity-rejection attack-path-rejection
  conclusion-mismatch-rejection challenge-target-rejection
  unknown-status-rejection duplicate-group-id-rejection
  group-repeated-member-rejection group-too-few-members-rejection
  group-member-undeclared-rejection admission-prune open-obligation
)

tmp_dir="$(mktemp -d)"
candidate=""
cleanup() {
  if [ -n "$candidate" ]; then
    rm -f "$candidate"
  fi
  rm -rf "$tmp_dir"
}
trap cleanup EXIT HUP INT TERM

[ -s "$manifest" ] || { echo "surface conformance: FAIL: empty manifest" >&2; exit 1; }
expected_manifest_header=$'case_id\tprogram\tpolicy\texpected\tfeatures'
actual_manifest_header="$(head -n 1 "$manifest")"
[ "$actual_manifest_header" = "$expected_manifest_header" ] || {
  echo "surface conformance: FAIL: manifest header mismatch" >&2; exit 1;
}

known_csv="$(IFS=,; printf '%s' "${required_features[*]}")"
awk -F '\t' -v known="$known_csv" '
  BEGIN { n = split(known, ks, ","); for (i = 1; i <= n; i++) allowed[ks[i]] = 1 }
  NR == 1 { next }
  NF != 5 { printf "surface conformance: FAIL: manifest row %d has %d columns\n", NR, NF > "/dev/stderr"; bad = 1; next }
  $1 == "" || $2 == "" || $3 == "" || $4 == "" || $5 == "" {
    printf "surface conformance: FAIL: manifest row %d has an empty cell\n", NR > "/dev/stderr"; bad = 1
  }
  {
    m = split($5, fs, ",")
    for (i = 1; i <= m; i++) {
      if (!(fs[i] in allowed)) {
        printf "surface conformance: FAIL: unknown feature %s in case %s\n", fs[i], $1 > "/dev/stderr"; bad = 1
      }
      seen[fs[i]] = 1
    }
  }
  END {
    for (k in allowed) if (!(k in seen)) {
      printf "surface conformance: FAIL: required feature not covered: %s\n", k > "/dev/stderr"; bad = 1
    }
    exit bad
  }
' "$manifest"

tail -n +2 "$manifest" | cut -f1 > "$tmp_dir/manifest.ids"
[ -s "$tmp_dir/manifest.ids" ] || { echo "surface conformance: FAIL: manifest has no cases" >&2; exit 1; }

cd "$repo_root"
if ! cabal build exe:surface-conformance > "$tmp_dir/cabal-build.log" 2>&1; then
  echo "surface conformance: FAIL: cabal build exe:surface-conformance" >&2
  cat "$tmp_dir/cabal-build.log" >&2
  exit 1
fi
if ! (cd lean && lake build surface-conformance) > "$tmp_dir/lake-build.log" 2>&1; then
  echo "surface conformance: FAIL: lake build surface-conformance" >&2
  cat "$tmp_dir/lake-build.log" >&2
  exit 1
fi

haskell_bin="$(cabal list-bin exe:surface-conformance)"
lean_bin="$repo_root/lean/.lake/build/bin/surface-conformance"
[ -x "$haskell_bin" ] || { echo "surface conformance: FAIL: missing Haskell emitter" >&2; exit 1; }
[ -x "$lean_bin" ] || { echo "surface conformance: FAIL: missing Lean emitter" >&2; exit 1; }

"$haskell_bin" --manifest "$manifest" > "$tmp_dir/haskell.tsv"
"$lean_bin" --manifest "$manifest" > "$tmp_dir/lean.tsv"

# Test-only fault injection: alter exactly the first Haskell data row's AST
# fingerprint so the gate suite can prove that update mode refuses divergence.
if [ "${SURFACE_CONFORMANCE_TEST_MUTATE_HASKELL_OUTPUT:-0}" = 1 ]; then
  awk 'BEGIN { FS = OFS = "\t" } NR == 2 { $2 = "0000000000000000" } { print }' \
    "$tmp_dir/haskell.tsv" > "$tmp_dir/haskell.mutated.tsv"
  mv "$tmp_dir/haskell.mutated.tsv" "$tmp_dir/haskell.tsv"
fi

expected_header=$'case_id\tast_fingerprint\toutcome\tcore_fingerprint\tobligations\tattacks\tobservations'
for output in "$tmp_dir/haskell.tsv" "$tmp_dir/lean.tsv"; do
  [ -s "$output" ] || { echo "surface conformance: FAIL: empty output: $output" >&2; exit 1; }
  [ "$(head -n 1 "$output")" = "$expected_header" ] || {
    echo "surface conformance: FAIL: output header mismatch: $output" >&2; exit 1;
  }
  tail -n +2 "$output" | cut -f1 > "$output.ids"
  if ! diff -u --label manifest.ids --label output.ids "$tmp_dir/manifest.ids" "$output.ids"; then
    echo "surface conformance: FAIL: missing, extra, or reordered output rows" >&2
    exit 1
  fi
done

if [ "$mode" = update ]; then
  if ! diff -u --label haskell.tsv --label lean.tsv "$tmp_dir/haskell.tsv" "$tmp_dir/lean.tsv"; then
    echo "surface conformance: FAIL: emitters differ; refusing golden update" >&2
    exit 1
  fi
  golden_dir="$(cd "$(dirname "$golden")" && pwd)"
  golden_base="$(basename "$golden")"
  candidate="$(mktemp "$golden_dir/.${golden_base}.tmp.XXXXXX")"
  cp "$tmp_dir/lean.tsv" "$candidate"
  if [ -e "$golden" ]; then
    chmod --reference="$golden" "$candidate"
  else
    chmod 0644 "$candidate"
  fi
  sync "$candidate"
  if [ "${SURFACE_CONFORMANCE_TEST_FAIL_BEFORE_RENAME:-0}" = 1 ]; then
    echo "surface conformance: FAIL: injected pre-rename failure" >&2
    exit 1
  fi
  mv -f "$candidate" "$golden"
  candidate=""
  printf 'surface conformance: UPDATED (%s cases)\n' "$(wc -l < "$tmp_dir/manifest.ids" | tr -d ' ')"
  exit 0
fi

[ -s "$golden" ] || { echo "surface conformance: FAIL: missing or empty golden: $golden" >&2; exit 1; }
for runtime in lean haskell; do
  if ! diff -u --label surface-conformance.golden --label "$runtime.tsv" "$golden" "$tmp_dir/$runtime.tsv"; then
    echo "surface conformance: FAIL: $runtime output differs from golden" >&2
    exit 1
  fi
done
printf 'surface conformance: PASS (%s cases)\n' "$(wc -l < "$tmp_dir/manifest.ids" | tr -d ' ')"
