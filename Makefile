# Convenience targets. The repo's source of truth stays cabal + scripts/;
# these wrap the common entry points.

.PHONY: build test doctest docs docs-haskell docs-lean bench bench-map bench-image bench-container measure presentation-parity surface-conformance surface-conformance-gate-test semantics-goldens semantics-registry semantics-registry-test backend-deps-golden update-goldens update-differential differential admission-differential ara-source-spans ara-session-index map-check map-conformance pw-conformance lean-build pw-example axiom-withdrawal-example axiom-audit lean-gate cross-check local-gates

build:
	cabal build all
	cd lean && lake build

test:
	cabal test all --test-show-details=direct

# The `>>>` examples in Haddock comments are executable and must stay true.
# `lara-doctest` is a cabal test-suite whose build-tool dependency is the
# doctest executable, so `cabal test all` (and CI) already runs it and nothing
# has to be installed by hand; this target runs just that suite. doctest stands
# in for GHC inside a nested `cabal repl lib:lara`, which reconfigures the
# library in interactive mode — the next `cabal build` reconfigures it back,
# so expect one extra configure step after a doctest run.
doctest:
	cabal test lara-doctest --test-show-details=direct

# ---------------------------------------------------------------------------
# API documentation, both halves. Nothing here is committed; each target prints
# where its index.html landed.
#
#   make docs             # both
#   make docs-haskell     # Haddock for the library, with hyperlinked source
#   make docs-lean        # doc-gen4 for lean/, via the lean/docbuild side project
#
# The Lean docs are a separate Lake project (lean/docbuild/) so that doc-gen4's
# own dependencies never enter lean/lakefile.toml: `lake build` for the proofs
# stays offline. The first run clones doc-gen4 from GitHub and builds it, which
# takes a few minutes; later runs are incremental.
docs: docs-haskell docs-lean

docs-haskell:
	cabal haddock --haddock-hyperlink-source lib:lara
	@echo "Haddock: $$(find dist-newstyle -path '*/doc/html/lara/index.html' | head -1)"

docs-lean:
	cd lean/docbuild && lake build Lara:docs
	@echo "doc-gen4: lean/docbuild/.lake/build/doc/index.html"

# ---------------------------------------------------------------------------
# Gates outside the required CI (docs/ci-scope-decision.md). The required
# `Haskell` workflow gates the Haskell compiler only; everything below needs a Lean build. Run them locally
# before asking for review on any change that touches lean/, a wire contract,
# or a golden either side emits:
#
#   make lean-gate      # proofs, axiom audit, semantics registry
#   make cross-check    # every Haskell-Lean conformance and differential gate
#   make local-gates    # both, in that order
#
# `lean-gate` is also what the optional Lean workflow (.github/workflows/lean.yml)
# runs on a PR carrying the `lean` label.

lean-gate: lean-build pw-example axiom-withdrawal-example axiom-audit semantics-registry semantics-registry-test

cross-check: presentation-parity surface-conformance surface-conformance-gate-test semantics-goldens backend-deps-golden update-goldens update-differential differential admission-differential map-conformance pw-conformance

local-gates: lean-gate cross-check

lean-build:
	cd lean && lake build

pw-example:
	python3 scripts/check-pw-example.py

axiom-withdrawal-example:
	python3 scripts/check-axiom-withdrawal.py

# `pipefail` is required, not cosmetic: without it the pipeline reports only
# check-axioms.sh's status, so a Lean failure that still emits some reports
# (e.g. `#print axioms` naming a renamed or deleted theorem) would be masked and
# the audit would go green over a silently reduced set. Coverage is a `find`,
# not a list (#242): a new module must not be able to join the tree unaudited.
axiom-audit:
	cd lean && bash -c 'set -eo pipefail; \
	  ../scripts/test-check-axioms.sh; \
	  python3 ../scripts/test_check_axcheck_coverage.py; \
	  python3 ../scripts/check-axcheck-coverage.py AxCheck.lean $$(find Lara -name "*.lean" | sort); \
	  lake env lean AxCheck.lean | ../scripts/check-axioms.sh'

# The fixture/example/bundle wire differential and the semantic admission
# differential over the test fixtures.
differential:
	bash scripts/differential.sh

admission-differential:
	bash scripts/admission-differential.sh

# Cross-language presentation-AST shape parity (result 12): both runtimes emit
# the same normalized ordered inventory, protected by compiler witnesses and
# shape tripwires; the gate rebuilds both and diffs them.
presentation-parity:
	bash scripts/check-presentation-parity.sh

# Independently parse/lower the concrete surface in Haskell and construct/check
# the matching presentation AST in Lean, then compare both canonical tables to
# one committed manifest-complete golden.
surface-conformance:
	bash scripts/check-surface-conformance.sh

# Regression tests for atomic update, failed-update cleanup, and check-mode
# immutability. All update exercises use a private temporary golden.
surface-conformance-gate-test:
	bash test/surface-conformance-gate.sh

# Lean-emitted extension-semantics goldens must match the checked-in Haskell
# conformance table byte for byte.
semantics-registry:
	python3 scripts/check-semantics-registry.py

semantics-registry-test:
	python3 -m unittest scripts/test_check_semantics_registry.py -v

semantics-goldens:
	bash scripts/check-semantics-goldens.sh

# The Lean-emitted `certDeps` of the shipped nd@1/ord@1 mixed term must match
# the committed golden byte for byte; test/StrictSpec.hs asserts the same bytes
# from the Haskell collector. Both halves run on the shipped backend cores — the
# ord@1 acceptance blocker does not reach a dependency report.
backend-deps-golden:
	bash scripts/check-backend-deps-golden.sh

# Lean-emitted source-update matrices must match the committed report byte for
# byte. Pass UPDATE=1 to regenerate the golden deterministically.
update-goldens:
	bash scripts/check-update-goldens.sh $(if $(UPDATE),--update,check)

# Haskell and Lean must agree on every finite constructor-precondition input
# generated by their native Lara.Update mirrors.
update-differential:
	bash scripts/update-differential.sh

# Every repository-local path:line[-line] quotation in the ARA must still match
# the cited source span.
ara-source-spans:
	python3 scripts/check_ara_source_spans.py

# Every session file under ara/trace/sessions/ has exactly one index row and no
# id is listed twice (#337). Stdlib-only; reads ara/, changes nothing.
# Needs PyYAML (the gate's one non-stdlib dependency, #338); CI runs the same
# script under `uv run --with pyyaml`.
ara-session-index:
	python3 scripts/check_ara_session_index.py

# Check one multi-artifact map (#303). PHONY on purpose: a map is a RECHECK, not
# a build, so this must run every time it is invoked — GNU Make guarantees that
# for a phony target, and a map has no output file whose timestamp could stand
# in for its members'. That matters because an edit which preserves a member's
# mtime still changes the verdict; nothing here is cached, pinned, or compared
# against a previous run.
#
#   make map-check                                  # the shipped D3 map
#   make map-check MAP=path/to/other.laramap
#   make map-check OUT=/tmp/map.verdict.sexp        # write the verdict instead
#
# With OUT set, `lara check --out` atomically replaces that file on success
# only; a refused map exits nonzero, Make stops, and the previous file is left
# exactly as it was. OUT's directory must already exist — the temporary that
# becomes it is created there, and nothing here creates directories. OUT is the
# same "where the output goes" variable `bench` below takes, declared there.
# `@` and `-v0` keep the recipe line and cabal's build log off stdout, so
# `make map-check > verdict.sexp` writes the VERDICT rather than the verdict
# preceded by a build log. That redirect is not the documented way to capture a
# verdict — OUT= is, and it bypasses stdout entirely — but it is the obvious
# thing to try, and a target whose stdout is not the artifact is a trap for
# anyone who tries it. Errors still reach stderr and still stop Make.
MAP ?= examples/agreement-map-multi/map.laramap
map-check:
	@cabal run -v0 exe:lara -- check "$(MAP)" $(if $(OUT),--out "$(OUT)",)

# Both drivers must agree on every committed map anchor, and the Lean decoder
# must refuse every malformed envelope. The map's counterpart of
# scripts/differential.sh; `make cross-check` runs it.
map-conformance:
	bash scripts/check-map-conformance.sh

# The possible-world outer runtime (#322): `lara pw` and the Lean `pw-run`
# reference must print the same bytes and exit codes on every committed
# fixtures/pw/run/ document and on every mutation case the script generates.
# Pass UPDATE=1 to regenerate the committed goldens (only after both agree).
pw-conformance:
	python3 scripts/check-pw-conformance.py $(if $(UPDATE),--update,)

# E1 checker-performance bench (issue #69): measures the production checker
# on the frozen corpus units and the manifest-discovered harness, prints the
# performance table, and writes the raw measurements/bench.json (gitignored).
#
# No rendered table is committed here — a table is only valid for the machine
# and commit that produced it. Print the one the consumer needs:
#
#   make bench
#   make bench FORMAT=markdown
#   make bench FORMAT=latex OUT=../paper/tables/performance.tex
FORMAT ?= text
OUT ?=
bench:
	cabal build exe:lara exe:lara-bench
	cd lean && lake build
	cabal run exe:lara-bench -- --format=$(FORMAT) $(if $(OUT),--out $(OUT),)

# Multi-artifact map bench (issue #319): a SECOND protocol, never a row of the
# kernel table above. A map reads, parses and rechecks several members, then
# links and checks again, so its cost scales with its member count rather than
# with one unit's size, and folding it into `bench`'s rows would make a kernel
# number mean something else. Every accepted conformance anchor is measured;
# the raw record is measurements/bench-map.json (gitignored). Text or markdown
# only, and no Lean build: nothing Lean runs.
#
#   make bench-map
#   make bench-map FORMAT=markdown
bench-map:
	cabal build exe:lara-bench
	cabal run exe:lara-bench -- --map --format=$(FORMAT) $(if $(OUT),--out $(OUT),)

BENCH_IMAGE ?= lara-bench:$(shell git rev-parse --short=12 HEAD)
BENCH_ARGS ?=
bench-image:
	docker build --platform linux/arm64 --build-arg LARA_GIT_REV=$(shell git rev-parse HEAD) -f containers/bench/Dockerfile -t $(BENCH_IMAGE) .

bench-container:
	python3 scripts/bench_container.py $(BENCH_ARGS)

# The full axis-(c) measurement harness (M5): measurements/report.{json,tsv}
# and ablation reports.
measure:
	cabal exec -- runghc scripts/measure.hs
