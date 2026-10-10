#!/usr/bin/env bash
# Run the Lean `process-run` reference over every committed process-input 1
# fixture and compare stdout byte for byte with its golden. The exit code must
# be the one the golden's envelope fixes (0 for process-result, 1 for the
# unsupported and limit-exceeded refusals, 2 for every other refusal), and
# stderr must stay empty. UPDATE=1 rewrites the goldens from the current runner.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
dir="$root/fixtures/process/run"
(cd "$root/lean" && lake build process-run >/dev/null)
bin="$root/lean/.lake/build/bin/process-run"
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
    "(process-result 1 "*) want=0 ;;
    "(process-error 1 unsupported "*|"(process-error 1 limit-exceeded "*) want=1 ;;
    *) want=2 ;;
  esac
  if [[ "$code" != "$want" ]]; then
    echo "FAIL $name: exit $code, expected $want"; fail=1
  fi
done
if [[ "$fail" != 0 ]]; then exit 1; fi
echo "process-run: $count fixtures match their goldens"
