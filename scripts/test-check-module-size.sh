#!/usr/bin/env bash
# Regression tests for scripts/check-module-size.sh (issue #161).
#
# The guard's whole value is that it fails where the old documentation-only
# rule silently passed, so the cases that matter are the failing ones: a module
# over the bound, and a sizing table that disagrees with reality in either
# direction. The comment-immunity case is the point of the revised rule — a
# module that is mostly Haddock must pass where `wc -l` would have failed it.
#
# Each case builds a throwaway repository shaped like the real one (a
# src/Lara/Mutate.hs plus a docs/ record with a sizing table) and runs the guard
# inside it with lowered thresholds.
set -euo pipefail

cd "$(dirname "$0")/.."
CHECK="$PWD/scripts/check-module-size.sh"
failures=0

# Build a fixture repo: $1 = module body, $2 = table rows, $3 = sigma row.
# Echoes the directory.
make_fixture() {
  local body="$1" rows="$2" sigma="$3"
  local dir
  dir="$(mktemp -d)"
  # The child directory must exist even when empty: a missing scope root is a
  # hard error by design (the namespace moved), and without it every case below
  # would "fail" on that error rather than on the condition under test.
  mkdir -p "$dir/src/Lara/Mutate" "$dir/docs"
  printf '%s\n' "$body" >"$dir/src/Lara/Mutate.hs"
  {
    printf '# fixture record\n\n'
    printf '## Sizing rule\n\n'
    printf '| Module | Lines | Code |\n|---|---|---|\n'
    printf '%s\n' "$rows"
    printf '%s\n' "$sigma"
  } >"$dir/docs/mutate-module-ownership-decision.md"
  printf '%s\n' "$dir"
}

# Runs the guard quietly, stashing its output in $guard_output so an
# unexpected verdict can show why. Reporting it unconditionally would bury the
# case verdicts under the failure messages the expect_fail cases exist to
# produce.
guard_output=''
run_guard() {
  local dir="$1"
  guard_output="$(
    cd "$dir"
    WARN_CODE_LINES="${WARN:-4}" FAIL_CODE_LINES="${FAIL:-6}" bash "$CHECK" 2>&1
  )"
}

expect_pass() {
  local name="$1" dir="$2"
  if run_guard "$dir"; then
    echo "PASS: $name"
  else
    echo "FAIL: $name (expected acceptance, got rejection)" >&2
    printf '%s\n' "$guard_output" | sed 's/^/    /' >&2
    failures=$((failures + 1))
  fi
  rm -rf "$dir"
}

expect_fail() {
  local name="$1" dir="$2"
  if run_guard "$dir"; then
    echo "FAIL: $name (expected rejection, got acceptance)" >&2
    printf '%s\n' "$guard_output" | sed 's/^/    /' >&2
    failures=$((failures + 1))
  else
    echo "PASS: $name"
  fi
  rm -rf "$dir"
}

# A 3-code-line module: module header, one signature, one binding.
small_body='module Lara.Mutate (a) where

import Data.List (sort)

a :: Int
a = 1'

# The same three code lines buried in Haddock and a block comment. Total lines
# balloon past the bound; code lines do not. `wc -l` would reject this.
commented_body='-- | A module that explains itself at length.
--
-- Every one of these lines used to count against the bound, which is how a
-- two-line review clarification took the root to 401 and shipped that way.
--
-- More prose. More prose. More prose. More prose. More prose. More prose.
-- More prose. More prose. More prose. More prose. More prose. More prose.
{- A block comment
   spanning
   several lines. -}
{-# LANGUAGE GHC2021 #-}
module Lara.Mutate (a) where

import Data.List
  ( sort
  , nub
  )

-- | The only real code here.
a :: Int
a = 1'

# Seven code lines, over the fixture FAIL threshold of 6.
big_body='module Lara.Mutate (a, b, c) where

a :: Int
a = 1

b :: Int
b = 2

c :: Int
c = 3'

expect_pass "small module, table current" \
  "$(make_fixture "$small_body" '| `Lara.Mutate` | 6 | 3 |' '| **Σ** | **6** | **3** |')"

expect_pass "comment-heavy module passes on code lines" \
  "$(make_fixture "$commented_body" '| `Lara.Mutate` | 21 | 3 |' '| **Σ** | **21** | **3** |')"

expect_fail "module over the code-line bound" \
  "$(make_fixture "$big_body" '| `Lara.Mutate` | 10 | 7 |' '| **Σ** | **10** | **7** |')"

expect_fail "table code count disagrees with reality" \
  "$(make_fixture "$small_body" '| `Lara.Mutate` | 6 | 99 |' '| **Σ** | **6** | **99** |')"

expect_fail "table total count disagrees with reality" \
  "$(make_fixture "$small_body" '| `Lara.Mutate` | 99 | 3 |' '| **Σ** | **99** | **3** |')"

expect_fail "module in scope has no table row" \
  "$(make_fixture "$small_body" '| `Lara.Mutate.Ghost` | 6 | 3 |' '| **Σ** | **6** | **3** |')"

expect_fail "table row names a module that does not exist" \
  "$(make_fixture "$small_body" \
    '| `Lara.Mutate` | 6 | 3 |
| `Lara.Mutate.Ghost` | 1 | 1 |' '| **Σ** | **6** | **3** |')"

expect_fail "sigma row disagrees with the measured totals" \
  "$(make_fixture "$small_body" '| `Lara.Mutate` | 6 | 3 |' '| **Σ** | **6** | **4** |')"

# The warn tier must not fail the build: 5 code lines is over WARN=4, under
# FAIL=6. This is the case the old single-hard-bound rule got wrong.
warn_body='module Lara.Mutate (a, b) where

a :: Int
a = 1

b :: Int
b = 2'

WARN=4 FAIL=6 expect_pass "warn tier warns without failing" \
  "$(make_fixture "$warn_body" '| `Lara.Mutate` | 7 | 5 |' '| **Σ** | **7** | **5** |')"

if [ "$failures" -gt 0 ]; then
  echo "FAIL: $failures case(s) in scripts/check-module-size.sh regression tests." >&2
  exit 1
fi

echo "PASS: scripts/check-module-size.sh regression tests"
