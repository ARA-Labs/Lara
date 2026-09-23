#!/usr/bin/env bash
# Regression tests for scripts/check-axioms.sh.
#
# Guards both repaired false-negative paths:
#   - a non-standard axiom reported on a continuation line must be rejected;
#   - a producer that fails after valid output must fail the whole pipeline.
# Empty or unrelated stdin must fail rather than producing a vacuous green
# audit.
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

run_documented_pipeline() {
  local producer_status="$1" input="$2"
  PRODUCER_STATUS="$producer_status" PRODUCER_INPUT="$input" bash -c '
    lake() {
      if [ "$#" -ne 3 ]; then
        return 64
      fi
      if [ "$1" != "env" ] || [ "$2" != "lean" ] || [ "$3" != "AxCheck.lean" ]; then
        return 64
      fi
      printf "%s\n" "$PRODUCER_INPUT"
      return "$PRODUCER_STATUS"
    }
    (set -o pipefail; cd lean && lake env lean AxCheck.lean | ../scripts/check-axioms.sh)
  '
}

expect_pipeline_pass() {
  local name="$1" producer_status="$2" input="$3"
  if run_documented_pipeline "$producer_status" "$input" >/dev/null 2>&1; then
    echo "PASS: $name"
  else
    echo "FAIL: $name (expected pipeline success, got failure)" >&2
    failures=$((failures + 1))
  fi
}

expect_pipeline_fail() {
  local name="$1" producer_status="$2" input="$3"
  if run_documented_pipeline "$producer_status" "$input" >/dev/null 2>&1; then
    echo "FAIL: $name (expected pipeline failure, got success)" >&2
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

valid_report="'Lara.foo' depends on axioms: [propext, Classical.choice, Quot.sound]"
expect_pipeline_pass "zero-exit producer" 0 "$valid_report"
expect_pipeline_fail "failing producer after valid output" 42 "$valid_report"

# A `#print axioms` naming a declaration that no longer exists does not remove a
# report -- it adds an `Unknown constant` error while every other line still
# reports normally. Rejecting on the reports alone is therefore not enough: the
# audit must reject the input itself, so that a theorem cannot silently leave
# the audited set via a rename, deletion, or typo.
expect_fail "unknown constant alongside valid reports" \
  "$valid_report
AxCheck.lean:3:14: error(lean.unknownIdentifier): Unknown constant \`Lara.PW.gone\`"

expect_fail "positionless lean error alongside valid reports" \
  "$valid_report
error: unknown module prefix 'Lara'"

# The same input, checked without any producer status available -- the saved
# output path from this script's usage line, where pipefail cannot help.
expect_fail "unknown constant in saved output" \
  "AxCheck.lean:9:14: error(lean.unknownIdentifier): Unknown constant \`Lara.PW.gone\`
$valid_report"

# Errors must be distinguished from Lean's routine linter warnings, and from
# audited theorems whose NAMES contain the word "error".
expect_pass "linter warning alongside valid reports" \
  "$valid_report
AxCheck.lean:12:4: warning: unused variable \`h\`"

expect_pass "theorem name containing 'error'" \
  "'Lara.Examples.check_child_error_precedes_parent_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lara.Examples.unit_error_reject_classes' does not depend on any axioms"

if [ "$failures" -gt 0 ]; then
  echo "$failures test(s) failed" >&2
  exit 1
fi
echo "All check-axioms tests passed."
