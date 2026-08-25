#!/usr/bin/env bash
# Executable guard for the `Lara.Mutate` namespace sizing rule (issue #161).
#
# `docs/mutate-module-ownership-decision.md` states the rule without wiggle
# room, but until now nothing measured it: `Lara.Mutate` went to 401 lines
# during the #158 review and shipped that way, found only by a reviewer running
# `wc -l` by hand. The record's sizing table was the sole guard, and it was
# itself stale in the same commit. This script replaces both halves of that
# failure with a check.
#
# WHAT IT MEASURES — code lines, not `wc -l`
#
#   A line counts when it is not blank, not a comment, not a pragma, and not an
#   import (continuation lines of a multi-line import list included). The module
#   header and its export list DO count: the public surface is part of a
#   module's weight.
#
#   Raw `wc -l` was the wrong meter. The 401-line breach was caused by a
#   two-line Haddock clarification *asked for in review*, and was repaired by
#   reflowing prose to buy the line back — the metric driving the work instead
#   of the reverse. In a project whose value rests on auditable, documented
#   semantics, a rule that charges a contributor for explaining themselves is
#   aimed at the wrong quantity. Code lines keep every seam the rule has found
#   (Outcome, Sites.Cert/Nav, Accept/Ops/Build) while making a comment free.
#
#   This is the same measure #143 already used to verify its split was
#   byte-preserving: "every non-comment, non-import code line of the original
#   file is present in the union of the three new files".
#
# TWO TIERS
#
#   Warn at WARN_CODE_LINES, fail at FAIL_CODE_LINES. The source guideline is
#   itself two-tier — split when exceeding 400, prohibited over 800 — and the
#   namespace record collapsed it into a single hard bound. Restoring the tiers
#   means a review comment can never break the build, while growth that
#   genuinely needs a seam still stops the gate.
#
# SCOPE — deliberately not repo-wide
#
#   The sizing rule is a `Lara.Mutate` decision, not a repository invariant.
#   Eleven modules elsewhere in src/ exceed 400 lines by design, three of them
#   past the source guideline's own 800-line prohibition (Lara.Syntax at 2136,
#   Lara.Wire at 1579, Lara.BindingAudit at 1365). A repo-wide sweep would fail
#   instantly on a third of the codebase, which is not what "guard the
#   documented rule" means. Adding a namespace to SCOPE_ROOTS is therefore a
#   decision that belongs in a docs/ record first.
#
# TABLE FRESHNESS
#
#   The record's sizing table is also checked against measured reality, in both
#   columns, in both directions (a row with no module, a module with no row).
#   That is the half of #161 that would have caught the stale table.
#
# Usage:
#   scripts/check-module-size.sh          # from the repository root
#
# The thresholds are overridable from the environment so that
# scripts/test-check-module-size.sh can exercise both tiers against a small
# fixture tree instead of a 300-line one. Do not override them in CI.
set -euo pipefail

WARN_CODE_LINES="${WARN_CODE_LINES:-250}"
FAIL_CODE_LINES="${FAIL_CODE_LINES:-300}"

RECORD="${RECORD:-docs/mutate-module-ownership-decision.md}"

# Roots whose *.hs files the rule covers. A plain file or a directory.
SCOPE_ROOTS=(src/Lara/Mutate.hs src/Lara/Mutate)

# Count code lines: skip blanks, comments, block comments, pragmas, and
# imports including their bracketed continuations.
code_lines() {
  awk '
    function count(s, ch,   n, i) {
      n = 0
      for (i = 1; i <= length(s); i++) if (substr(s, i, 1) == ch) n++
      return n
    }
    {
      line = $0
      sub(/^[[:space:]]+/, "", line)

      if (inblock) { if (line ~ /-\}/) inblock = 0; next }

      if (inimport) {
        depth += count(line, "(") - count(line, ")")
        if (depth <= 0) inimport = 0
        next
      }

      if (line == "") next
      if (line ~ /^--/) next
      if (line ~ /^\{-#/) next
      if (line ~ /^\{-/) { if (line !~ /-\}/) inblock = 1; next }

      # An import list may open on the line *after* the import itself:
      #
      #     import Lara.Mutate
      #       ( Expected (..)
      #       , Mutant (..)
      #       )
      #
      # so a bracket-balance check on the import line alone misses it and
      # counts the whole list as code. Look at the next significant line.
      if (pendingimport) {
        pendingimport = 0
        if (line ~ /^[(]/ || line ~ /^hiding/) {
          depth = count(line, "(") - count(line, ")")
          if (depth > 0) inimport = 1
          next
        }
      }

      if (line ~ /^import([[:space:]]|$)/) {
        depth = count(line, "(") - count(line, ")")
        if (depth > 0) inimport = 1
        else pendingimport = 1
        next
      }

      n++
    }
    END { print n + 0 }
  ' "$1"
}

# src/Lara/Mutate/Sites/Cert.hs -> Lara.Mutate.Sites.Cert
module_name() {
  local path="${1#src/}"
  path="${path%.hs}"
  printf '%s\n' "$path" | tr '/' '.'
}

# Lara.Mutate.Sites.Cert -> src/Lara/Mutate/Sites/Cert.hs
module_path() {
  printf 'src/%s.hs\n' "$(printf '%s' "$1" | tr '.' '/')"
}

# Just the rows of the "## Sizing rule" table. The ownership tables earlier in
# the record list the same module names (with `(internal)` suffixes) and are a
# different contract; matching them here would compare export lists to line
# counts. `### ` subsections stay inside the slice, `## ` ends it.
sizing_table_rows() {
  awk '/^## Sizing rule/ { inside = 1; next }
       inside && /^## / { inside = 0 }
       inside && /^\| `Lara\.Mutate/ { print }' "$RECORD"
}

files=()
for root in "${SCOPE_ROOTS[@]}"; do
  if [ -f "$root" ]; then
    files+=("$root")
  elif [ -d "$root" ]; then
    while IFS= read -r f; do
      files+=("$f")
    done < <(find "$root" -name '*.hs' | sort)
  else
    echo "::error::scope root does not exist: $root" >&2
    exit 1
  fi
done

if [ "${#files[@]}" -eq 0 ]; then
  echo "::error::sizing guard matched no modules — check SCOPE_ROOTS." >&2
  exit 1
fi

failures=0
warnings=0

printf '%-32s %7s %7s\n' 'MODULE' 'LINES' 'CODE'

measured_total=0
measured_code=0
declare -a seen_modules=()

for f in "${files[@]}"; do
  name="$(module_name "$f")"
  total="$(wc -l <"$f" | tr -d ' ')"
  code="$(code_lines "$f")"
  seen_modules+=("$name")
  measured_total=$((measured_total + total))
  measured_code=$((measured_code + code))

  flag=''
  if [ "$code" -gt "$FAIL_CODE_LINES" ]; then
    flag='  <-- OVER'
    failures=$((failures + 1))
  elif [ "$code" -gt "$WARN_CODE_LINES" ]; then
    flag='  <-- approaching'
    warnings=$((warnings + 1))
  fi
  printf '%-32s %7s %7s%s\n' "$name" "$total" "$code" "$flag"

  if [ "$code" -gt "$FAIL_CODE_LINES" ]; then
    echo "::error::$name has $code code lines, over the ${FAIL_CODE_LINES}-line bound for the Lara.Mutate namespace ($RECORD). Split it along a seam, or amend the record." >&2
  elif [ "$code" -gt "$WARN_CODE_LINES" ]; then
    echo "::warning::$name has $code code lines, approaching the ${FAIL_CODE_LINES}-line bound (warn at $WARN_CODE_LINES). Plan the seam now, before the next operator forces it." >&2
  fi
done

printf '%-32s %7s %7s\n' 'Σ' "$measured_total" "$measured_code"

# --- table freshness -------------------------------------------------------
#
# Rows look like:  | `Lara.Mutate.Sites.Cert` | 141 | 68 |
# The Σ row is bolded and is checked separately.

if [ ! -f "$RECORD" ]; then
  echo "::error::sizing record not found: $RECORD" >&2
  exit 1
fi

documented=0
while IFS='|' read -r _ raw_name raw_total raw_code _; do
  name="$(printf '%s' "$raw_name" | tr -d ' `')"
  doc_total="$(printf '%s' "$raw_total" | tr -d ' ')"
  doc_code="$(printf '%s' "$raw_code" | tr -d ' ')"
  [ -n "$name" ] || continue
  documented=$((documented + 1))

  path="$(module_path "$name")"
  if [ ! -f "$path" ]; then
    echo "::error::$RECORD sizing table lists $name, which has no module at $path." >&2
    failures=$((failures + 1))
    continue
  fi

  real_total="$(wc -l <"$path" | tr -d ' ')"
  real_code="$(code_lines "$path")"
  if [ "$doc_total" != "$real_total" ] || [ "$doc_code" != "$real_code" ]; then
    echo "::error::$RECORD sizing table says $name is $doc_total/$doc_code (lines/code); it measures $real_total/$real_code." >&2
    failures=$((failures + 1))
  fi
done < <(sizing_table_rows)

for name in "${seen_modules[@]}"; do
  if ! sizing_table_rows | grep -qF "| \`$name\` |"; then
    echo "::error::$name is in scope but has no row in the $RECORD sizing table." >&2
    failures=$((failures + 1))
  fi
done

if [ "$documented" -eq 0 ]; then
  echo "::error::found no sizing-table rows in $RECORD — has the table moved or changed shape?" >&2
  exit 1
fi

sigma_row="$(grep -E '^\| \*\*Σ\*\*' "$RECORD" || true)"
if [ -z "$sigma_row" ]; then
  echo "::error::$RECORD sizing table has no Σ row." >&2
  failures=$((failures + 1))
elif ! printf '%s' "$sigma_row" | grep -qF "**$measured_total**" \
  || ! printf '%s' "$sigma_row" | grep -qF "**$measured_code**"; then
  echo "::error::$RECORD sizing table Σ row disagrees with the measured totals ($measured_total lines, $measured_code code)." >&2
  failures=$((failures + 1))
fi

# --- verdict ---------------------------------------------------------------

if [ "$failures" -gt 0 ]; then
  echo "FAIL: $failures sizing problem(s); see the errors above." >&2
  exit 1
fi

if [ "$warnings" -gt 0 ]; then
  echo "PASS (with $warnings warning(s)): every module in the Lara.Mutate namespace is within $FAIL_CODE_LINES code lines, and the $RECORD sizing table is current."
else
  echo "PASS: every module in the Lara.Mutate namespace is within $FAIL_CODE_LINES code lines, and the $RECORD sizing table is current."
fi
