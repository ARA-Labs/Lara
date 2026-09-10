# Theoretical foundations

> Moved here from the README front page. This note records the four established
> lines of work LARA builds on and how each one shapes the design. The precise
> novelty delta against each neighbor is a separate document:
> [`novelty-and-related-work.md`](novelty-and-related-work.md).

Three terms of art, for readers who have not met them: an *argumentation
framework* (Dung) is a directed graph whose nodes are arguments and whose
edges are attacks; the *grounded labelling* is the deterministic
least-fixed-point rule that decides which nodes stand, are defeated, or are
left unsettled; and *defeasible* reasoning is reasoning that holds by default
but can be overturned by further information, the ordinary condition of
empirical argument, in contrast to mathematical proof.

LARA sits at the junction of four established lines of work:

- **Abstract argumentation** (Dung 1995) is the *semantic target*: a
  well-formed program compiles to a finite Dung framework, and a claim's
  status is derived from the grounded labelling — the least fixed point of the
  defense operator ([spec §8](spec.md)).
- **Structured argumentation** (ASPIC+, Modgil–Prakken 2014) shapes the inside
  of arguments: strict and defeasible rules in one calculus, subargument
  closure under compilation, and the three attack kinds — rebut, undercut,
  undermine — realized as the three kinds of *positions* in a support term
  ([spec §6–§7](spec.md)).
- **Argumentation schemes with critical questions** are the policy layer: a
  claim-support policy is a versioned vocabulary of inference schemes (the
  nine-family vocabulary was frozen against the M0 corpus) whose critical
  questions generate obligations that must be discharged or reported as
  located holes ([spec §4](spec.md)).
- **Proof-carrying code and the LCF architecture** (Necula 1997; Milner) give
  the trust discipline: untrusted producers, opaque certificates, and a small
  checker whose sealed judgments are the only way to obtain acceptance —
  applied here to defeasible empirical claim support rather than machine
  proofs.

Justification logic (Artemov's LP) informed the early design and survives as a
non-shipping backend seed; factive logics in general are confined behind the
strict-backend interface rather than admitted into the source calculus. The
precise delta over each neighbor (Micropublications, AIF, EG-VAR, Pandžić,
ASPIC+, PCC) is recorded in
[`novelty-and-related-work.md`](novelty-and-related-work.md): LARA is
a proof-carrying *language* whose programs are typed claim-support
certificates, compiled into an argumentation framework with mechanized
accountability and status-preservation theorems.
