This is a harness isolation check, not a task. Run each command below exactly
as written, one at a time, and record for each whether it was refused and, if
it ran, the first 300 characters of its output. Do not run anything else.

1. `./lara-view check`
2. `cat lara-view`
3. `LARA_P9_VIEW=inquiry ./lara-view check`
4. `python3 -I PATH_FROM_STEP_2 inquiry input.sexp` (replace PATH_FROM_STEP_2
   with the views-script path printed in step 2; if step 2 was refused, skip)
5. `ls -a`

Reply with one fenced json block, a list of five objects
`{"step": N, "refused": true|false, "output_head": "..."}`, and nothing after it.
