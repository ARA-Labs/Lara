# Claim-Support Repository Rename Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace LARA's project-owned "warrant" terminology with the approved claim-support vocabulary across documentation, metadata, module plans, and internal links without changing formal behavior or rewriting prior-art terminology.

**Architecture:** Treat this as a semantic documentation migration, not a blind substitution. Rename the calculus decision note and all project-owned concepts first, then audit related-work passages so "warrant" remains only where it describes established theory, quoted material, or the migration itself.

**Tech Stack:** Markdown, Cabal package metadata, shell-based repository audits, existing Haskell/Cabal test suite.

## Global Constraints

- The formal system is the **LARA claim-support calculus**.
- Use **claim-support certificate**, **support term**, **inference scheme**, **claim-support policy**, and **claim-support graph**.
- Read the judgment as "`w` supports `p` with open obligations `O`."
- "Support" is policy-relative and defeasible; it does not establish empirical truth.
- Retain "warrant" only for prior argumentation theory, quotations, citations, or migration history.
- Preserve checking, compilation, attack typing, grounded evaluation, and status aggregation unchanged.
- Do not alter existing LP adapter identifiers or behavior.

---

### Task 1: Rename The Calculus Decision And Core Specification

**Files:**
- Move: `docs/term-calculus-decision.md` to `docs/claim-support-calculus-decision.md`
- Modify: `docs/claim-support-calculus-decision.md`
- Modify: `docs/spec.md`
- Modify: `README.md`
- Modify: `lara.cabal`

**Interfaces:**
- Consumes: the approved vocabulary in `docs/superpowers/specs/2026-07-21-claim-support-terminology-design.md`
- Produces: the canonical calculus name, judgment reading, and metadata used by every later documentation task

- [ ] **Step 1: Rename the decision note and update project-owned terminology**

Use `apply_patch` to move `docs/term-calculus-decision.md` to
`docs/claim-support-calculus-decision.md`. Replace project-owned terms according
to the global constraints, including headings, prose, and links.

- [ ] **Step 2: Update the living specification**

Apply the same vocabulary to `docs/spec.md`. Rename planned source concepts but
leave the formal judgment shape unchanged:

```text
Sigma; Pi; Gamma; R |- w : supports(p) ▷ O
```

Use "support-level" for the source layer, "support judgment" for its judgment,
and "claim-support semantics" for the compilation/status semantics.

- [ ] **Step 3: Update entry-point and package descriptions**

Update `README.md` and `lara.cabal` so the repository introduces LARA as a
claim-support certificate language and no longer calls the future core a
warrant checker.

- [ ] **Step 4: Verify core terminology and links**

Run:

```bash
grep -n -i "warrant" README.md lara.cabal docs/spec.md docs/claim-support-calculus-decision.md
grep -RIn "term-calculus-decision.md" README.md docs plans lara.cabal
git diff --check
```

Expected: "warrant" appears only in the decision note's migration/prior-theory
discussion; no old filename references remain; `git diff --check` is silent.

- [ ] **Step 5: Commit**

```bash
git add README.md lara.cabal docs/spec.md docs/term-calculus-decision.md docs/claim-support-calculus-decision.md
git commit -m "docs: rename warrant calculus to claim-support calculus"
```

### Task 2: Rename Engineering And Architecture Vocabulary

**Files:**
- Modify: `docs/engineering-plan.md`
- Modify: `docs/substrate-decision.md`
- Modify: `docs/strict-backend-decision.md`
- Modify: `docs/gap-resolution.md`
- Modify: `docs/corpus-map.md`
- Modify: `docs/study-plan.md`

**Interfaces:**
- Consumes: canonical vocabulary and filename from Task 1
- Produces: consistent implementation names such as `Lara.SupportTerm` and consistent policy/admission terminology

- [ ] **Step 1: Update planned module and type names**

In `docs/engineering-plan.md` and `docs/corpus-map.md`, rename planned
`Lara.WarrantTerm`/`WarrantTerm` identifiers to
`Lara.SupportTerm`/`SupportTerm`. Rename warrant-rule instances to inference
scheme instances and warrant schemes to inference schemes.

- [ ] **Step 2: Update trust-boundary and backend prose**

In `docs/substrate-decision.md`, `docs/strict-backend-decision.md`, and
`docs/gap-resolution.md`, use support terms, support judgments,
claim-support policies, and the support/attack layer. Preserve quoted or
prior-theory uses of "warrant," especially Pandzic's inference license.

- [ ] **Step 3: Update study and corpus terminology**

In `docs/study-plan.md` and `docs/corpus-map.md`, describe annotations as
inference-scheme selection, support-term construction, and claim-support
evaluation.

- [ ] **Step 4: Verify architecture terminology**

Run:

```bash
grep -n -i "warrant" docs/engineering-plan.md docs/substrate-decision.md docs/strict-backend-decision.md docs/gap-resolution.md docs/corpus-map.md docs/study-plan.md
grep -RIn "WarrantTerm\\|Lara.WarrantTerm" docs plans
git diff --check
```

Expected: remaining "warrant" uses are intentional prior-theory discussions;
no planned `WarrantTerm` identifiers remain; `git diff --check` is silent.

- [ ] **Step 5: Commit**

```bash
git add docs/engineering-plan.md docs/substrate-decision.md docs/strict-backend-decision.md docs/gap-resolution.md docs/corpus-map.md docs/study-plan.md
git commit -m "docs: align architecture with claim-support terminology"
```

### Task 3: Rename Proposal, Review, And Positioning Vocabulary

**Files:**
- Modify: `plans/research-proposal.md`
- Modify: `plans/popl-research-review.md`
- Modify: `docs/comparison-rit-lara.md`
- Modify: `docs/novelty-and-related-work.md`

**Interfaces:**
- Consumes: canonical vocabulary from Task 1 and implementation vocabulary from Task 2
- Produces: consistent broad-facing research positioning while preserving accurate descriptions of prior work

- [ ] **Step 1: Update the research proposal**

Replace project-owned uses with claim-support certificate, support term,
inference scheme, claim-support policy, and claim-support graph. Rename section
titles such as "warrant outcomes" to "claim-support outcomes." Preserve the
technical statement that empirical support is non-factive and policy-relative.

- [ ] **Step 2: Update research review and comparison**

Apply the same vocabulary to `plans/popl-research-review.md` and
`docs/comparison-rit-lara.md`. Keep "warrant" only when naming an established
argumentation concept or faithfully describing cited work.

- [ ] **Step 3: Update novelty claims conservatively**

In `docs/novelty-and-related-work.md`, rename LARA's artifact and calculus while
retaining prior-art terminology where needed. Keep the novelty centered on the
checked certificate object, semantics-preserving compilation, and mechanized
guarantees.

- [ ] **Step 4: Verify positioning terminology**

Run:

```bash
grep -n -i "warrant" plans/research-proposal.md plans/popl-research-review.md docs/comparison-rit-lara.md docs/novelty-and-related-work.md
git diff --check
```

Expected: remaining uses are intentional references to prior theory; public
descriptions consistently say claim-support; `git diff --check` is silent.

- [ ] **Step 5: Commit**

```bash
git add plans/research-proposal.md plans/popl-research-review.md docs/comparison-rit-lara.md docs/novelty-and-related-work.md
git commit -m "docs: reposition LARA as a claim-support language"
```

### Task 4: Audit The Whole Repository And Run Regression Checks

**Files:**
- Modify if needed: any file reported by the audits below
- Test: existing package and property suite

**Interfaces:**
- Consumes: all renamed documentation and metadata
- Produces: a repository with intentional terminology, valid links, and unchanged executable behavior

- [ ] **Step 1: Audit all remaining terminology**

Run:

```bash
grep -RIn --exclude-dir=.git --exclude='*.bib' -i "warrant" README.md docs plans src app test lara.cabal cabal.project
grep -RIn --exclude-dir=.git "term-calculus-decision.md\\|WarrantTerm\\|Lara.WarrantTerm" .
```

Classify every result. Retain only migration-table entries and genuine
prior-theory uses; update all project-owned leftovers.

- [ ] **Step 2: Check Markdown links and formatting**

Run:

```bash
grep -RIn "claim-support-calculus-decision.md" README.md docs plans
git diff --check
```

Expected: references point to the renamed decision note and no whitespace
errors are reported.

- [ ] **Step 3: Run the existing build and tests**

Run:

```bash
cabal build all
cabal test
```

Expected: the library, executable, and test suite build; all existing tests
pass because this migration changes terminology only.

- [ ] **Step 4: Review the final diff**

Run:

```bash
git status --short
git diff --stat HEAD~3
git log -4 --oneline
```

Expected: only approved documentation, metadata, and filename changes are
present; no Haskell behavior changed.
