# Heuristics

## H01: Prove one generic frame-stream inverse before the recursive AST inverse
- **Rationale**: Framing every token as `UTF8_BYTE_LENGTH:PAYLOAD` reduces delimiter,
  Unicode, truncation, and trailing-input reasoning to one reusable
  `decodeFrames (renderFrames xs) = some xs` theorem. The Atom proof then reasons
  structurally over decoded fields instead of reparsing raw strings at every constructor.
- **Provenance**: ai-suggested
- **Sensitivity**: medium
- **Code ref**: ["lean/Lara/Strict.lean", "src/Lara/Strict/ND.hs"]

## H02: Separate executable matrices from soundness-facing proofs
- **Rationale**: Lean `native_decide` is convenient for external String evaluation but
  introduces generated axioms. Runtime matrices should remain executable `Bool` definitions
  enforced by `#guard`, so a false matrix fails the build without entering the theorem TCB;
  audited soundness theorems should cross `replay_iff` and construct `HasType` witnesses
  explicitly.
- **Provenance**: ai-suggested
- **Sensitivity**: high
- **Code ref**: ["lean/Lara/Strict.lean", "lean/Lara/Examples.lean", "lean/AxCheck.lean"]
- **Last revised**: 2026-07-25 (2026-07-25_002)

## H03: Store raw matcher bindings and normalize only at equality boundaries
- **Rationale**: A contrary matcher must remain exact for an arbitrary canonicalizer,
  not merely an idempotent one. Retaining the first raw ground term and applying
  `nfTerm canon` exactly once to it and the comparison term enforces repeated-variable
  equality without silently assuming `canon (canon s) = canon s`.
- **Provenance**: ai-suggested
- **Sensitivity**: high
- **Code ref**: ["lean/Lara/Attack.lean", "lean/Lara/Examples.lean"]

## H04: Retain proof-bearing support results across the attack pass
- **Rationale**: A whole-program checker should infer each declared support term
  exactly once, retain an index-aligned `List CheckedSupport`, and transport the
  cached proof to an attack source through a named structural-equality witness.
  This prevents diagnostic drift and duplicated backend replay while making the
  compile-boundary proof fields direct consequences of checker soundness.
- **Provenance**: ai-suggested
- **Sensitivity**: high
- **Code ref**: ["lean/Lara/Check/Program.lean", "lean/Lara/Check/Attack.lean"]

## H05: Keep executable recursion first-order and move dependent adequacy proofs beside it
- **Rationale**: Lean can accept a dependent proof-carrying recursion into an
  `.olean` while its C-code generation path still revisits and times out on the
  dependent proof terms. A first-order `Except` checker plus a proof-only
  companion module preserves executable code generation, exact
  soundness/completeness, and readable stage boundaries.
- **Provenance**: ai-suggested
- **Sensitivity**: high
- **Code ref**: ["lean/Lara/Check/Support.lean", "lean/Lara/Check/SupportProof.lean"]
