#!/usr/bin/env bash
# Run the Lean `inquiry-run` reference over every committed inquiry-input 1
# fixture and compare stdout byte for byte with its golden. The exit code must
# be the one the golden's envelope fixes (0 for inquiry-result, 1 for the
# unsupported and limit refusals, 2 for every other refusal), and stderr must
# stay empty. UPDATE=1 rewrites the goldens from the current runner.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
dir="$root/fixtures/process/inquiry"
(cd "$root/lean" && lake build inquiry-run >/dev/null)
bin="$root/lean/.lake/build/bin/inquiry-run"
fail=0
count=0
for input in "$dir"/*.sexp; do
  name=$(basename "$input" .sexp)
  golden="$dir/$name.expected"
  err=$(mktemp)
  set +e
  out=$("$bin" "$input" 2>"$err")
  code=$?
  set -e
  count=$((count + 1))
  if [[ -s "$err" ]]; then
    echo "FAIL $name: stderr not empty"; cat "$err"; fail=1
  fi
  rm -f "$err"
  if [[ "${UPDATE:-}" == 1 ]]; then
    printf '%s\n' "$out" > "$golden"
  fi
  if [[ ! -f "$golden" ]]; then
    echo "FAIL $name: no golden"; fail=1; continue
  fi
  if [[ "$out" != "$(cat "$golden")" ]]; then
    echo "FAIL $name: output differs from golden"
    diff <(printf '%s\n' "$out") "$golden" || true
    fail=1
  fi
  case "$(cat "$golden")" in
    "(inquiry-result 1 "*) want=0 ;;
    "(inquiry-error 1 () (unsupported "*|"(inquiry-error 1 () (limit "*) want=1 ;;
    *) want=2 ;;
  esac
  if [[ "$code" != "$want" ]]; then
    echo "FAIL $name: exit $code, expected $want"; fail=1
  fi
done
# The usage and io refusals happen at the executable boundary, before any
# document is read, so no fixture can reach them: drive them by argument shape.
boundary() {
  local name=$1 want=$2
  shift 2
  local err out code
  err=$(mktemp)
  set +e
  out=$("$bin" "$@" 2>"$err")
  code=$?
  set -e
  count=$((count + 1))
  if [[ -s "$err" ]]; then
    echo "FAIL $name: stderr not empty"; cat "$err"; fail=1
  fi
  rm -f "$err"
  # shellcheck disable=SC2053 # $want is a glob pattern on purpose
  if [[ "$out" != $want ]]; then
    echo "FAIL $name: unexpected output: $out"; fail=1
  fi
  if [[ "$code" != 2 ]]; then
    echo "FAIL $name: exit $code, expected 2"; fail=1
  fi
}
usage='(inquiry-error 1 () (usage "*"))'
boundary usage-no-args "$usage"
boundary usage-two-args "$usage" "$dir/p0-verdict.sexp" "$dir/p0-verdict.sexp"
boundary io-missing-file '(inquiry-error 1 () (io "*"))' "$dir/does-not-exist.sexp"
if [[ "$fail" != 0 ]]; then exit 1; fi
echo "inquiry-run: $count fixtures and boundary cases match"
python3 "$root/scripts/check_inquiry_bytes.py"
python3 "$root/scripts/check_inquiry_products.py"
