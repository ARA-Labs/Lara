#!/usr/bin/env bash
# Axiom audit for `#print axioms` output (AxCheck.lean).
#
# Reads the checker output on stdin and fails (exit 1) if:
#   - the input contains no Lean declaration reports,
#   - any proof depends on `sorryAx` (a sorry/admit slipped in), or
#   - any `[...]` axiom list names an axiom outside the standard trio
#     (propext, Classical.choice, Quot.sound).
#
# Multiline reports are normalized before each `[...]` list is extracted, so
# an axiom split across lines cannot evade the check.
#
# Usage:
#   (cd lean && lake env lean AxCheck.lean | ../scripts/check-axioms.sh)
#   scripts/check-axioms.sh < saved-output.txt
set -euo pipefail

out="$(cat)"

printf '%s\n' "$out"

if ! grep -Eq "^'[^']+' (depends on axioms:|does not depend on any axioms)" <<<"$out"; then
  echo "::error::Axiom audit received no Lean declaration reports." >&2
  exit 1
fi

if grep -q 'sorryAx' <<<"$out"; then
  echo "::error::A proof depends on sorryAx (sorry/admit)." >&2
  exit 1
fi

bad="$(printf '%s\n' "$out" \
  | tr '\n' ' ' \
  | grep -oE '\[[^]]*\]' \
  | tr -d '[]' | tr ',' '\n' | sed 's/^[[:space:]]*//;s/[[:space:]]*$//' \
  | grep -vE '^(propext|Classical\.choice|Quot\.sound)$' \
  | grep -v '^$' || true)"

if [ -n "$bad" ]; then
  echo "::error::A proof depends on a non-standard axiom: $bad" >&2
  exit 1
fi

echo "Axiom audit passed."
