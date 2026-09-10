#!/usr/bin/env bash
# Regenerate fixtures/ANCHORS.tsv, the committed list of byte-parity anchors
# scripts/differential.sh pins its glob against.
#
# Run after adding or removing a `.sexp` anchor under fixtures/, examples/,
# bundles/ or corpus-units/. The script that consumes it fails when the tree and
# the manifest disagree, so this is the one step that makes a new anchor part of
# the differential rather than a setup failure.
#
# The exclusions below are the same four the discovery loop applies, and they
# are exclusions of whole FAMILIES with their own harnesses, not of individual
# names: fixtures/malformed/ is the negative half of this script,
# fixtures/mutants/ is discovered manifest-driven, fixtures/admission/ belongs to
# scripts/admission-differential.sh, and a map's two committed artifacts are
# map-check-input@1 and map-verdict@1 rather than check-input@1 and belong to
# scripts/check-map-conformance.sh.
#
# Usage:  bash scripts/gen-anchor-manifest.sh
# Exit:   0 on success; 2 if a required root is missing or the result is empty.
set -u

repo_root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$repo_root" || exit 2

manifest="fixtures/ANCHORS.tsv"
listing="$(mktemp "${TMPDIR:-/tmp}/lara-anchors.XXXXXX")" || exit 2
trap 'rm -f "$listing"' EXIT

for root in fixtures examples bundles corpus-units; do
  if [ ! -d "$root" ]; then
    echo "FAIL: required anchor root is not a directory: $root"
    exit 2
  fi
done

if ! find fixtures examples bundles corpus-units -name '*.sexp' \
  -not -path 'fixtures/malformed/*' \
  -not -path 'fixtures/mutants/*' \
  -not -path 'fixtures/admission/*' \
  -not -name 'map.core.sexp' \
  -not -name 'map.verdict.sexp' \
  -print | LC_ALL=C sort >"$listing"; then
  echo "FAIL: could not discover anchors"
  exit 2
fi

if [ ! -s "$listing" ]; then
  echo "FAIL: discovery found no anchors; refusing to write an empty manifest"
  exit 2
fi

{
  sed -n '/^#/p' "$manifest" 2>/dev/null
  cat "$listing"
} >"$manifest.new"

# Keep the header even on a first run, when there is no manifest to read one
# from — an unexplained bare list is exactly the artifact this discipline is
# meant to replace.
if ! grep -q '^#' "$manifest.new"; then
  echo "FAIL: $manifest has no header comment to preserve; write one first"
  rm -f "$manifest.new"
  exit 2
fi

mv "$manifest.new" "$manifest"
printf 'wrote %s (%s anchors)\n' "$manifest" "$(grep -c -v '^#' "$manifest")"
