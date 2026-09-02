#!/usr/bin/env bash
# Axiom audit for `#print axioms` output (AxCheck.lean).
#
# Reads the checker output on stdin and fails (exit 1) if:
#   - the input contains a Lean error diagnostic (see below),
#   - the input contains no Lean declaration reports,
#   - any proof depends on `sorryAx` (a sorry/admit slipped in), or
#   - any `[...]` axiom list names an axiom outside the standard trio
#     (propext, Classical.choice, Quot.sound).
#
# Multiline reports are normalized before each `[...]` list is extracted, so
# an axiom split across lines cannot evade the check.
#
# The error-diagnostic check exists because `#print axioms` naming a
# declaration that does not exist is NOT a missing report — it is an `error:
# Unknown constant` on stderr while every *other* line still reports normally.
# Without this check the audit reads those surviving reports, finds nothing
# wrong with them, and prints "Axiom audit passed." So a theorem could silently
# leave the audit — renamed, deleted, or mistyped — and the gate would stay
# green over the reduced set. Lean's exit status catches that too, but only
# when the caller uses the documented `set -o pipefail` form; this check also
# holds when the script is run against saved output, where there is no producer
# status to consult at all.
#
# Only *errors* are rejected. Lean linter warnings are routine here and are
# passed through. The pattern matches Lean's diagnostic shape
# (`file:line:col: error...`), never the bare word, because several audited
# theorems have `error` in their names (`check_child_error_precedes_parent_shape`).
#
# Usage:
#   (set -o pipefail; cd lean && lake env lean AxCheck.lean | ../scripts/check-axioms.sh)
#   scripts/check-axioms.sh < saved-output.txt
set -euo pipefail

out="$(cat)"

printf '%s\n' "$out"

diagnostics="$(grep -E '(:[0-9]+:[0-9]+: error|^error[:(])' <<<"$out" || true)"
if [ -n "$diagnostics" ]; then
  echo "::error::Axiom audit input contains Lean errors; the reported set is incomplete." >&2
  printf '%s\n' "$diagnostics" >&2
  exit 1
fi

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
