# `lara-core@0.2` regeneration diffs (issue #89, D11)

Two diffs are the *measurement* of this pass, not an assertion about it. Both
are committed here with "empty" as the claim, so a future regeneration that
moves either one is visible in review rather than silently absorbed.

Commands, run against the pre-#89 tree (`dfa9811~1`) and the post-#89 tree:

```
# 1. the expected-column diff over the 369 PRE-EXISTING mutants
git show dfa9811~1:fixtures/mutants/MANIFEST.tsv | cut -f1,5 | sort            > old.tsv
cut -f1,5 fixtures/mutants/MANIFEST.tsv | sort \
  | grep -vE 'undeclared-pred|wrong-pred-arity|wrong-arg-sort|undeclared-con|wrong-theta-sort|out-of-scope-var' > new.tsv
diff old.tsv new.tsv

# 2. the verdict + status diff over all 60 corpus expected.json files
#    (compare `verdict-class` and the located-diagnostic status list per unit)
extract() {
  python3 -c 'import json,sys; d=json.load(open(sys.argv[1])); print(sys.argv[1], d["verdict-class"], sorted((s["claim"], s["status"]) for s in d["located-diagnostic"].get("statuses", [])))' "$1"
}
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
mkdir "$tmp/old"
files=$(git ls-files 'corpus-units/**/expected.json')
for f in $files; do extract "$f"; done > "$tmp/new.txt"
git archive dfa9811~1 corpus-units | tar -x -C "$tmp/old"
(cd "$tmp/old" && for f in $files; do extract "$f"; done) > "$tmp/old.txt"
[ "$(wc -l < "$tmp/new.txt")" -eq 60 ] &&
  [ "$(wc -l < "$tmp/old.txt")" -eq 60 ] ||
  { echo "extraction failed: expected 60 rows in each output" >&2; exit 1; }
diff -u "$tmp/old.txt" "$tmp/new.txt"
```

## 1. `MANIFEST.tsv` expected-column diff, 369 pre-existing mutants

```
(empty)
```

**Why it is empty, and why that was not free.** Three operator groups synthesize
fresh symbols: `hidden-contrary` injects `mut_p`/`mut_q`, the accept family
injects its own contraries and premises, and `rebut-cycle` builds the whole
`mutation-cycles-v1` vocabulary. Under a naive port each would have flipped to
R2 — stripping R12 of its only mutation family and destroying the accept
family's status × attack-kind coverage matrix. The fix is #89 §8's design
commitment: **the operator that injects a symbol is the site that knows its
argument sorts**, so each extends the mutant's carried Σ. A mutant therefore
tests the class it seeds.

Two class-boundary decisions carry the rest of the zero: a θ key *off* the
parameter list stays R3 (`wrong-subst-domain`, 19 mutants), and an instance
whose rule id does not resolve stays R1 (`hidden-rule`, 19 mutants). Had stage 2
been scoped to include θ-domain totality or rule-id lookup, both families would
have moved and the paper's per-class table with them.

## 2. Corpus verdict + status diff, all 60 units

```
(empty)
```

This is strict mode's real risk, discharged: an over-tight Σ that silently
rejected a valid corpus unit would read as a checker improvement, and D11
*regenerates* `expected.json`, so it would have written the flip straight into
the new baseline. Comparing across the regeneration boundary is what catches it.

## Excluded from regeneration

`measurements/binding-audit/**` is frozen input (#89 §8, decision D-5). Its
sealed identity hashes the exact bytes of `worklist.tsv`, leaf-results, and
object-results — not corpus `.sexp` bytes — and no worklist column carries the
core version. Verified before regenerating: re-running the worklist derivation
reproduced the committed `worklist.tsv` byte-for-byte, so the wire bump cannot
reach the 38-leaf denominator.
