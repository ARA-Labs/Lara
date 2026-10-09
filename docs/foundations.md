# Theoretical foundations

This note records the four established lines of work Lara builds on and how
each one shapes the design. How Lara differs from each neighbor is in
[`novelty-and-related-work.md`](novelty-and-related-work.md).

Three terms of art, for readers who have not met them: an *argumentation
framework* (Dung) is a directed graph whose nodes are arguments and whose
edges are attacks; the *grounded labelling* is the deterministic
least-fixed-point rule that decides which nodes stand, are defeated, or are
left unsettled; and *defeasible* reasoning is reasoning that holds by default
but can be overturned by further information, the ordinary condition of
empirical argument, in contrast to mathematical proof.

Lara sits at the junction of four established lines of work:

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
  claim-support policy is a versioned vocabulary of inference schemes (a
  nine-family vocabulary covering the corpus) whose critical questions
  generate obligations that must be discharged or reported as located holes
  ([spec §4](spec.md)). Yu and Zenker (2020) note that evaluating a scheme
  instance completely means asking every critical question relevant to it,
  and propose a meta-level critical-question list for the general schema
  "premises; if premises then conclusion; so conclusion". Lara does not
  claim completeness in that general sense: the policy fixes which questions
  are mandatory, and completeness is relative to the policy ([spec §4.2](spec.md)).
- **Proof-carrying code and the LCF architecture** (Necula 1997; Milner) give
  the trust discipline: untrusted producers, opaque certificates, and a small
  checker whose sealed judgments are the only way to obtain acceptance —
  applied here to defeasible empirical claim support rather than machine
  proofs.

Justification logic (Artemov's LP) is not part of the source calculus; LP
could enter only as an optional strict backend adapter, which Lara does not
ship ([spec §5.2](spec.md)). Factive logics in general are confined behind the
strict-backend interface.
