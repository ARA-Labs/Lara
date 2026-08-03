# Convenience targets. The repo's source of truth stays cabal + scripts/;
# these wrap the common entry points.

.PHONY: build test bench measure

build:
	cabal build all
	cd lean && lake build

test:
	cabal test all --test-show-details=direct

# E1 checker-performance bench (issue #69): measures the production checker
# on the 60 frozen corpus units and the 420-record harness and regenerates
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
