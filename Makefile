# Convenience targets. The repo's source of truth stays cabal + scripts/;
# these wrap the common entry points.

.PHONY: build test bench measure presentation-parity

build:
	cabal build all
	cd lean && lake build

test:
	cabal test all --test-show-details=direct

# Cross-language presentation-AST shape parity (result 12): both runtimes emit
# the same normalized ordered inventory, protected by compiler witnesses and
# shape tripwires; the gate rebuilds both and diffs them.
presentation-parity:
	bash scripts/check-presentation-parity.sh

# E1 checker-performance bench (issue #69): measures the production checker
# on the frozen corpus units and the manifest-discovered harness, then regenerates
# tables/performance.tex (generated, never hand-typed) plus the raw
# measurements/bench.json.
bench:
	cabal build exe:lara
	cd lean && lake build
	cabal exec -- runghc scripts/bench.hs

# The full axis-(c) measurement harness (M5): measurements/report.{json,tsv}
# and ablation reports.
measure:
	cabal exec -- runghc scripts/measure.hs
