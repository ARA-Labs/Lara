#!/usr/bin/env bash
# Admission differential harness (metatheory plan Task 3).
#
# Runs the exact corpus declared by `fixtures/admission/MANIFEST` through BOTH
# semantic admission adapters — Haskell calls the production
# admission/prune primitives through `test/Lara/AdmissionFixture.hs`; Lean
# calls the proved evaluator through `lean/Lara/AdmissionDriver.lean`. The
# gate asserts byte-exact agreement on stdout, exit code, outcome class, and
# declared codec diagnostics. It does not claim `.lara` parser/elaborator or
# final public-verdict equivalence; `test/AdmissionSpec.hs` covers the real
# Haskell `prepareSource`/`runSourceCheck` seam.
#
# The manifest is also checked against the directory's exact `*.sexp` set:
# missing, duplicate, malformed, or unlisted fixtures fail before execution.
# Each non-codec fixture carries a committed `expected` outcome; both drivers
# verify it internally. Every `codec-reject` row pins a Haskell and a Lean
# stderr substring in addition to exit 2 and empty stdout.
#
# Usage:  bash scripts/admission-differential.sh
# Exit:   0 iff every fixture agrees (positive byte-parity AND the negative
#         exit-2/empty-stdout); 1 on any disagreement; 2 on a build/setup
#         error or when no fixtures were found (an empty corpus must never
#         be a green pass — it means fixtures/admission/ moved).
set -u

repo_root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$repo_root" || exit 2

tmp_dir="$(mktemp -d "${TMPDIR:-/tmp}/lara-admission-diff.XXXXXX")" || {
  echo "FAIL: cannot create temp dir" >&2
  exit 2
}
cleanup() {
  rm -rf "$tmp_dir"
}
trap cleanup EXIT
trap 'exit 129' HUP
trap 'exit 130' INT
trap 'exit 143' TERM

echo "== building both admission drivers"
# Build logs live in $tmp_dir, which the EXIT trap removes before we return —
# so on failure the log's tail must be dumped here, not referenced by path.
cabal_build_log="$tmp_dir/cabal-build.log"
if ! cabal build exe:lara >"$cabal_build_log" 2>&1; then
  echo "FAIL: cabal build failed; last lines of build log:" >&2
  tail -40 "$cabal_build_log" >&2
  exit 2
fi
lean_build_log="$tmp_dir/lean-build.log"
if ! ( cd lean && lake build admission-driver ) >"$lean_build_log" 2>&1; then
  echo "FAIL: lake build failed; last lines of build log:" >&2
  tail -40 "$lean_build_log" >&2
  exit 2
fi

hs_cmd=(cabal exec -- runghc --ghc-arg=-itest --ghc-arg=-package --ghc-arg=lara scripts/check-admission.hs)
lean_bin="lean/.lake/build/bin/admission-driver"
[ -x "$lean_bin" ] || { echo "FAIL: no Lean admission driver binary at $lean_bin"; exit 2; }

manifest="fixtures/admission/MANIFEST"
fixture_cases="$tmp_dir/fixture-cases.tsv"
actual_list="$tmp_dir/fixtures.actual"
sorted_manifest_list="$tmp_dir/fixtures.manifest"

if [ ! -f "$manifest" ]; then
  echo "FAIL: missing exact fixture manifest $manifest" >&2
  exit 2
fi
if ! awk -F '	' '
  /^[[:space:]]*($|#)/ { next }
  {
    if (NF != 4) {
      print "invalid manifest row " NR ": expected four tab-separated fields" > "/dev/stderr"
      bad = 1
      next
    }
    if ($1 !~ /^[A-Za-z0-9][A-Za-z0-9._-]*[.]sexp$/) {
      print "invalid manifest fixture at row " NR ": " $1 > "/dev/stderr"
      bad = 1
      next
    }
    if ($2 !~ /^(accepted|rejected|invalid|codec-reject)$/) {
      print "invalid manifest outcome at row " NR ": " $2 > "/dev/stderr"
      bad = 1
      next
    }
    if ($1 in seen) {
      print "duplicate manifest fixture at row " NR ": " $1 > "/dev/stderr"
      bad = 1
      next
    }
    if ($3 == "" || $4 == "") {
      print "empty manifest stderr marker at row " NR > "/dev/stderr"
      bad = 1
      next
    }
    if ($2 == "codec-reject" && ($3 == "-" || $4 == "-")) {
      print "codec-reject row lacks per-driver stderr markers at row " NR > "/dev/stderr"
      bad = 1
      next
    }
    if ($2 != "codec-reject" && ($3 != "-" || $4 != "-")) {
      print "non-codec row carries stderr markers at row " NR > "/dev/stderr"
      bad = 1
      next
    }
    seen[$1] = 1
    classes[$2] += 1
    print "fixtures/admission/" $1 "\t" $2 "\t" $3 "\t" $4
    count += 1
  }
  END {
    required[1] = "accepted"
    required[2] = "rejected"
    required[3] = "invalid"
    required[4] = "codec-reject"
    for (i = 1; i <= 4; i += 1) {
      if (classes[required[i]] == 0) {
        print "manifest has no " required[i] " fixture" > "/dev/stderr"
        bad = 1
      }
    }
    if (count == 0) {
      print "manifest declares no fixtures" > "/dev/stderr"
      bad = 1
    }
    if (bad) exit 1
  }
' "$manifest" >"$fixture_cases"; then
  echo "FAIL: invalid fixture manifest $manifest" >&2
  exit 2
fi
cut -f1 "$fixture_cases" | LC_ALL=C sort >"$sorted_manifest_list"
if ! find fixtures/admission -maxdepth 1 -type f -name '*.sexp' -print |
    LC_ALL=C sort >"$actual_list"; then
  echo "FAIL: cannot list fixtures/admission" >&2
  exit 2
fi
if ! cmp -s "$sorted_manifest_list" "$actual_list"; then
  echo "FAIL: fixtures/admission does not match $manifest" >&2
  diff "$sorted_manifest_list" "$actual_list" >&2
  exit 2
fi
expected_count="$(wc -l <"$fixture_cases" | tr -d '[:space:]')"

pass=0
fail=0
printf '\n%-42s  %-7s  %s\n' "fixture" "exit" "manifest + stdout parity"
printf -- '-----------------------------------------------------------------------------------\n'
while IFS="$(printf '\t')" read -r f expected_class hs_marker lean_marker; do
  case_name="$(basename "$f")"
  hs_out="$tmp_dir/hs.out"
  hs_err="$tmp_dir/hs.err"
  lean_out="$tmp_dir/lean.out"
  lean_err="$tmp_dir/lean.err"
  "${hs_cmd[@]}" "$f" >"$hs_out" 2>"$hs_err"
  hs_exit=$?
  "$lean_bin" "$f" >"$lean_out" 2>"$lean_err"
  lean_exit=$?
  if [ "$expected_class" = "codec-reject" ] &&
      [ -n "$hs_marker" ] && [ -n "$lean_marker" ] &&
      [ "$hs_exit" -eq 2 ] && [ "$lean_exit" -eq 2 ] &&
      [ ! -s "$hs_out" ] && [ ! -s "$lean_out" ] &&
      grep -Fq -- "$hs_marker" "$hs_err" &&
      grep -Fq -- "$lean_marker" "$lean_err"; then
    printf '%-42s  %-7s  %s\n' "$case_name" "2" "codec-reject + diagnostics"
    pass=$((pass + 1))
  elif [ "$expected_class" != "codec-reject" ] &&
      [ "$hs_exit" -eq 0 ] && [ "$lean_exit" -eq 0 ] &&
      cmp -s "$hs_out" "$lean_out" &&
      grep -q "^(${expected_class} " "$hs_out"; then
    printf '%-42s  %-7s  %s\n' "$case_name" "0" "$expected_class byte-identical"
    pass=$((pass + 1))
  else
    printf '%-42s  %-7s  %s\n' "$case_name" "$hs_exit/$lean_exit" "MISMATCH ($expected_class)"
    printf '  expected class %s; exit: haskell=%s lean=%s\n' \
      "$expected_class" "$hs_exit" "$lean_exit"
    if ! cmp -s "$hs_out" "$lean_out"; then
      echo "  stdout differs:"
      diff "$hs_out" "$lean_out" | head -4 | sed 's/^/    /'
    elif [ "$expected_class" != "codec-reject" ] && [ -s "$hs_out" ]; then
      echo "  stdout agrees but is not the expected outcome class:"
      sed 's/^/    /' "$hs_out"
    elif [ ! -s "$hs_out" ]; then
      echo "  both drivers produced empty stdout"
    fi
    # Always dump both stderr streams. A driver that exits non-zero (oracle
    # mismatch, codec error, crash) explains itself only on stderr, the temp
    # dir is removed by the EXIT trap, and the branches above can all be
    # silent — so an unprinted stderr is a permanently lost diagnostic.
    if [ -s "$hs_err" ]; then
      echo "  haskell stderr:"
      head -10 "$hs_err" | sed 's/^/    /'
    else
      echo "  haskell stderr: (empty)"
    fi
    if [ -s "$lean_err" ]; then
      echo "  lean stderr:"
      head -10 "$lean_err" | sed 's/^/    /'
    else
      echo "  lean stderr: (empty)"
    fi
    if [ "$expected_class" = "codec-reject" ]; then
      printf '  manifest markers: haskell=%s lean=%s\n' "$hs_marker" "$lean_marker"
    fi
    fail=$((fail + 1))
  fi
done <"$fixture_cases"

printf -- '-----------------------------------------------------------------------------------\n'
echo "pass=$pass fail=$fail expected=$expected_count"
[ "$fail" -eq 0 ] && [ "$pass" -eq "$expected_count" ]
