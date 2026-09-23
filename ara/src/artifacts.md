# Codebase pointer index

_Pointer index to the LARA repository codebase (code only). The repo is the linkable store; paths are
verified to exist as of 2026-07-21. Run records (test output) live in `evidence/`, not here._

## Lara.Prop — the implemented `nf`/`≡` normalizer (carve-out layer 1)
- **File(s) in repo**: `src/Lara/Prop.hs` (162 lines)
- **Nature**: Haskell library module — the trusted proposition identity relation.
- **What it does / contains**: ground first-order `Term`/`Prop` ASTs; `nf` (literal canonicalization +
  structural recursion, no argument reordering); `(===)`/`equiv`; `canonNum` (numeric-literal
  canonicalization); `prettyProp`/`prettyTerm`. `canonId` is `id` with Unicode NFC marked as the single
  deferred extension point. Transcribed into `execution/Prop.hs`.
- **How to use / run**: imported by the checker; exercised by `test/PropSpec.hs`.
- **Claims supported**: C01

## Lara.Kernel + Term + Formula + ConstantSpec — the LP adapter seed (non-conforming)
- **File(s) in repo**: `src/Lara/Kernel.hs` (130), `src/Lara/Term.hs` (46), `src/Lara/Formula.hs` (34),
  `src/Lara/ConstantSpec.hs` (60)
- **Nature**: Haskell library — an experimental Logic-of-Proofs proof-term checker with a sealed
  `Judgment`.
- **What it does / contains**: `Term` (justification polynomials `x | c | s·t | s+t | !t`), `Formula`
  (`p | ⊥ | F→G | t:F`), `ConstantSpec`/`Context`, and `check` (Const/Hyp/App/Sum-L/Sum-R/Check rules)
  minting a sealed `Judgment`. **Non-conforming**: `ConstantSpec` accepts arbitrary `(constant,
  formula)` pairs, so it does not recognize fixed LP axiom schemas and is not a valid strict adapter.
  Kernel transcribed into `execution/Kernel.hs`.
- **How to use / run**: `cabal run lara` (demo checks `(c0 · x) : Q`); exercised by `test/Spec.hs`.
- **Claims supported**: C03 (as the seed that motivated the backend interface; not the trusted core)

## Test suites
- **File(s) in repo**: `test/PropSpec.hs` (132 — the 8 `≡`-law/idempotence/no-reorder/`canonNum`
  properties), `test/Spec.hs` (177 — the 6 LP-seed properties + runner)
- **Nature**: QuickCheck property suites (the conformance-evidence layer for the implemented code).
- **What it does / contains**: generators for propositions/terms/LP derivations; the algebraic-law
  assertions. Runner prints one line per property.
- **How to use / run**: `cabal test`.
- **Claims supported**: C01 (PropSpec)

## Demo
- **File(s) in repo**: `app/Main.hs` (39)
- **Nature**: executable demo of the LP seed.
- **What it does / contains**: checks `(c0 · x) : Q` end-to-end via `Lara.Kernel.check`.
- **How to use / run**: `cabal run lara`.
- **Claims supported**: C03

## Specification and planning documents (the frozen calculus + trajectory)
- **File(s) in repo**: `docs/spec.md` (the calculus), `docs/strict-backend-decision.md`,
  `docs/claim-support-calculus-decision.md`, `docs/substrate-decision.md`, `docs/gap-resolution.md`,
  `docs/engineering-plan.md`, `docs/mechanization-plan.md`, `docs/worked-examples-plan.md`,
  `docs/corpus-map.md`, `docs/novelty-and-related-work.md`, `docs/prior-art-lessons.md`,
  `plans/lara-related-work.bib`.
- **Nature**: the design/theory content — the source of every claim, concept, and proof in this ARA.
- **What it does / contains**: the frozen v0.1 calculus (spec), the settled decisions, the milestone
  spine (M0–M7), the 12 required metatheory results, and the trajectory the trace reconstructs.
- **How to use / run**: read; `spec.md` is the contract every module implements.
- **Claims supported**: C01–C12 (all)
