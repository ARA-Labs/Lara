#!/usr/bin/env bash
# Regression tests for scripts/check-axioms.sh.
#
# Guards the repaired false-negative path: a non-standard axiom reported on a
# *continuation line* of a multiline `[...]` list must be rejected, and a
# multiline list containing only the standard trio must pass. Empty or
# unrelated stdin must fail rather than producing a vacuous green audit.
set -euo pipefail

cd "$(dirname "$0")/.."
CHECK=scripts/check-axioms.sh
failures=0

expect_pass() {
  local name="$1" input="$2"
  if printf '%s\n' "$input" | "$CHECK" >/dev/null 2>&1; then
    echo "PASS: $name"
  else
    echo "FAIL: $name (expected acceptance, got rejection)" >&2
    failures=$((failures + 1))
  fi
}

expect_fail() {
  local name="$1" input="$2"
  if printf '%s\n' "$input" | "$CHECK" >/dev/null 2>&1; then
    echo "FAIL: $name (expected rejection, got acceptance)" >&2
    failures=$((failures + 1))
  else
    echo "PASS: $name"
  fi
}

expect_pass "single-line standard trio" \
  "'Lara.foo' depends on axioms: [propext, Classical.choice, Quot.sound]"

expect_pass "multiline standard trio" \
  "'Lara.foo' depends on axioms: [propext,
   Classical.choice,
   Quot.sound]"

expect_fail "single-line non-standard axiom" \
  "'Lara.foo' depends on axioms: [propext, Fake.nonStandard]"

expect_fail "multiline non-standard axiom" \
  "'Lara.foo' depends on axioms: [propext,
   Fake.nonStandard]"

expect_fail "sorryAx" \
  "'Lara.foo' depends on axioms: [sorryAx]"

expect_fail "empty input" ""

expect_fail "unrelated input" \
  "Build completed successfully."

if [ "$failures" -gt 0 ]; then
  echo "$failures test(s) failed" >&2
  exit 1
fi
echo "All check-axioms tests passed."
