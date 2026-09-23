/-
Heterogeneous backend compositionality (`Lara.BackendComposition`) — milestone
B0's vocabulary layer, sitting on top of `Lara.Support`.

`Lara.Support` already proves that *one* certificate node is accounted for: its
conclusion follows from the reported slots of its own consulted context
(`cert_steps_accounted`), and the per-node reports collect into `certDeps`
(`mem_certDeps_step` / `certStep_deps_subset`). What it does not yet say is what
happens when a single support term carries certificate nodes from *several*
backend identities at once. That is this module's subject, and the reason it is
a separate file rather than more of `Lara/Support.lean` (already 1350 lines):
these declarations have their own vocabulary — an occurrence, the set of
identities a term names, the per-occurrence consequence — and their own reason
to be read alone (CLAUDE.md's module-seam rule).

The namespace is `Lara.BackendComposition`, deliberately *not* `Lara.Backend`:
this is not a sibling of `Lara.Strict.Backend`. A `Strict.Backend` is one
backend core; this module is about how several of them coexist in one term.

Nothing here changes an existing definition or theorem. `CertStepIn` remains the
induction principle; the additions are a statement surface over it.
-/

import Lara.Support

namespace Lara.BackendComposition

open Lara.Support

/-! ### Certificate occurrences as a record -/

/-- One certificate-assured instance node, with its node shape spread into
fields.

**Design note D1 (why a record).** `CertStepIn` (`Lara/Support.lean`) is a
relation over a node *pattern*: the `here` constructor matches
`.inst rn θ ws D H (.cert β hd κ)`, so every theorem that wants to say
"a certificate node occurring in `w`" has to re-spell eight binders and then
carry them through the statement — `cert_steps_accounted` and
`certDeps_resolved` both do exactly that, and both pay for it in their
signatures. Bundling the eight into a record makes the *statement* surface
readable while leaving the *induction* surface (`CertStepIn`) untouched.

**Deliberate deviation from the paper sketch.** The instantiated premise
conclusions and the node's source conclusion are **not** fields. They are not
part of the node's syntax: they are recovered from the rule and the
substitution, and exist only relative to a typing derivation
(`instAPats θ r.premises`, `instAPat θ r.concl`). Storing them would let a
caller forge an occurrence whose recorded premises disagree with the ones its
rule actually instantiates. They are derived from the derivation instead —
see `cert_steps_accounted`, which produces them. -/
structure CertOccurrence where
  /-- The rule name the instance uses. -/
  rn : RuleId
  /-- The wire substitution for the rule's parameters. -/
  θ  : Subst
  /-- The instance's premise subterms. -/
  ws : List SupportTerm
  /-- The instance's discharge map. -/
  D  : List (QuestionId × SupportTerm)
  /-- The instance's open holes. -/
  H  : List QuestionId
  /-- The certificate's backend identity — the `(name, version)` pair. -/
  β  : BackendId
  /-- The certificate's selected theory digest. -/
  hd : Digest
  /-- The opaque certificate reference. -/
  κ  : CertRef

/-- The support-term node an occurrence denotes. Definitionally the `here`
pattern of `CertStepIn`, so `CertStepIn.here` typechecks directly against
`OccursIn _ o`. -/
def CertOccurrence.node (o : CertOccurrence) : SupportTerm :=
  .inst o.rn o.θ o.ws o.D o.H (.cert o.β o.hd o.κ)

/-- `OccursIn w o`: the certificate occurrence `o` appears in `w` — at the
root, inside a premise subterm, or inside a discharge subterm. This is
`CertStepIn` with the node repackaged; the two are definitionally equal, so
proofs may still `induction` on the underlying `CertStepIn` derivation. -/
def OccursIn (w : SupportTerm) (o : CertOccurrence) : Prop :=
  CertStepIn w o.node

/-! ### Which backend identities a term names -/

/- The three carriers of `usedBackends`, mirroring `certDeps`
(`Lara/Support.lean`) structurally — same three shapes, same append order — so
the two collection proofs share a shape. -/
mutual
  /-- `usedBackends w`: every backend identity named by a certificate assurance
  anywhere in `w`, discharge subterms included.

  **Design note D2 (no registry parameter).** Unlike `certDeps`, this takes
  neither a rule context `Pi` nor a registry `reg`. The identity `β` sits on the
  node itself, inside `Assurance.cert`, so *which* backends a term names is
  readable from the term alone. That is a deliberate strengthening rather than
  an omission: it makes "this term uses `ord@1` and `nd@1`" a source-visible,
  checkable fact — decidable before any backend is looked up, let alone run.
  What a named backend *proves* of course needs the registry; that is
  `OccurrenceConsequence`. -/
  def usedBackends : SupportTerm → List BackendId
    | .leaf _ => []
    | .inst _ _ ws D _ α =>
        (match α with
         | .cert β _ _ => [β]
         | _ => []) ++ usedBackendsList ws ++ usedBackendsDis D
  /-- The premise-list carrier of `usedBackends`. -/
  def usedBackendsList : List SupportTerm → List BackendId
    | [] => []
    | w :: ws => usedBackends w ++ usedBackendsList ws
  /-- The discharge-map carrier of `usedBackends`. -/
  def usedBackendsDis : List (QuestionId × SupportTerm) → List BackendId
    | [] => []
    | (_, w) :: rest => usedBackends w ++ usedBackendsDis rest
end

/-! ### What one occurrence's backend actually establishes -/

/-- The consequence a single certificate occurrence's backend delivers: its
identity `β` resolves in the registry to a core, its digest `hd` resolves to
theory data `T`, and that core's own consequence relation holds of the
conclusion `C` from the reported slots of the full consulted context
`As ++ T` — the *semantic tail* of `cert_steps_accounted`'s conclusion, stated
per occurrence instead of inline. Only the tail: that theorem additionally
conjoins the rule-side facts (`Pi rn = some r`, the strict mode, the
`certifiers` allowlist, and the two instantiations) and binds `r`, `As` and the
conclusion existentially, where here `As` and `C` are parameters. Those
conjuncts stay in the typing derivation; this definition is deliberately the
weaker, purely semantic half, so that it can be stated of an occurrence without
re-deriving its rule.

**Design note D3 — where heterogeneity actually lives.** `registered.core.Form`
is bound by the `∃`. The formula type, the theory data `T`, and the consequence
relation `modelsFull` are all projections of a witness that this proposition
itself introduces and then discharges: each existential closes before the next
one opens. So when a term carries two occurrences and we conjoin their
consequences —
`OccurrenceConsequence reg β₁ hd₁ κ₁ As₁ C₁ ∧ OccurrenceConsequence reg β₂ hd₂ κ₂ As₂ C₂`
— **no binder in scope requires the two to share a formula type, a theory, or a
consequence relation.** That is the claim, and it is a claim about the *absence
of a relating binder*, not an assertion that the two are disjoint. A registry is
an arbitrary function `BackendId → Option (RegisteredBackend canon)`; nothing
stops it mapping two identities to the same core, in which case the two formula
types *are* equal. Type disjointness is therefore neither provable nor intended.
Heterogeneity here means the composition is *unconstrained*, not that the parts
are *distinct*: the source-level conclusions compose without any relation
between the backends' internal mathematics ever being asserted, and that is
precisely what makes the composition free.

Say what *is* shared, so the sentence above is not compressed into the false
"nothing is shared". Two binders do span both conjuncts: the registry `reg` and
the source canonicalizer `canon` that every `Backend canon` is indexed by. Both
are source-side — the registry is the closed table the program selects from, and
`canon` fixes source identity, which is what makes two backends' conclusions
*comparable as claims about the same source*. Neither relates the backends'
internal mathematics, so the three enumerated above remain unshared and the
claim stands. Sharing the canonicalizer is in fact what the composition needs:
without it the occurrences would be talking about different source languages. -/
def OccurrenceConsequence {canon : String → String} (reg : BackendRegistry canon)
    (β : BackendId) (hd : Digest) (κ : CertRef) (As : List Atom) (C : Atom) : Prop :=
  ∃ registered T, reg β = some registered ∧ registered.resolveTheory hd = some T ∧
    registered.core.modelsFull
      (Strict.selectSlots (As.map registered.core.enc ++ T) (registered.core.uses κ))
      (registered.core.enc C)

/-! ### `usedBackends` is exactly the occurrences' identities -/

/-- A backend named inside a premise subterm is named by the premise list.
Mirrors `certDeps_mem_list` (`Lara/Support.lean`). -/
theorem usedBackends_mem_list :
    ∀ {ws : List SupportTerm} {i : Nat} {w : SupportTerm} {β : BackendId},
      ws[i]? = some w → β ∈ usedBackends w → β ∈ usedBackendsList ws := by
  intro ws
  induction ws with
  | nil => intro i w β hw _; simp at hw
  | cons w₀ ws ih =>
    intro i w β hw hb
    cases i with
    | zero =>
      have : w₀ = w := by simpa using hw
      subst this
      exact List.mem_append.mpr (Or.inl hb)
    | succ k =>
      exact List.mem_append.mpr (Or.inr (ih (by simpa using hw) hb))

/-- A backend named inside a discharge subterm is named by the discharge map.
Mirrors `certDeps_mem_dis` (`Lara/Support.lean`). -/
theorem usedBackends_mem_dis :
    ∀ {D : List (QuestionId × SupportTerm)} {j : Nat} {q : QuestionId}
      {w : SupportTerm} {β : BackendId},
      D[j]? = some (q, w) → β ∈ usedBackends w → β ∈ usedBackendsDis D := by
  intro D
  induction D with
  | nil => intro j q w β hw _; simp at hw
  | cons qw rest ih =>
    intro j q w β hw hb
    obtain ⟨q₀, w₀⟩ := qw
    cases j with
    | zero =>
      have h0 : q₀ = q ∧ w₀ = w := by simpa using hw
      obtain ⟨_, rfl⟩ := h0
      exact List.mem_append.mpr (Or.inl hb)
    | succ k =>
      exact List.mem_append.mpr (Or.inr (ih (by simpa using hw) hb))

/-- Backends named by an occurring node are named by the surrounding term.
Mirrors `certStep_deps_subset` (`Lara/Support.lean`) — the same three
`List.mem_append` shuffles. -/
theorem certStep_usedBackends_subset {w u : SupportTerm}
    (hstep : CertStepIn w u) :
    ∀ β, β ∈ usedBackends u → β ∈ usedBackends w := by
  induction hstep with
  | here => intro β hb; exact hb
  | prem hw _ ih =>
    intro β hb
    exact List.mem_append.mpr
      (Or.inl (List.mem_append.mpr (Or.inr (usedBackends_mem_list hw (ih β hb)))))
  | dis hw _ ih =>
    intro β hb
    exact List.mem_append.mpr (Or.inr (usedBackends_mem_dis hw (ih β hb)))

/-- An occurrence names its own backend. -/
theorem usedBackends_node (o : CertOccurrence) : o.β ∈ usedBackends o.node := by
  simp [CertOccurrence.node, usedBackends]

/- Forward direction of `mem_usedBackends_iff`. `SupportTerm` nests its
recursive occurrences under `List`, so a plain `induction w` hands back no
induction hypothesis for the `ws`/`D` carriers: the subterm reached through
`ws[i]? = some w'` is not syntactically a component of the node. The list
companions therefore have to produce the *occurrence*, not merely an index, so
that the three theorems recurse through each other on genuine components —
the same mutual shape `Lara/Check/SupportProof.lean` uses for
`inferSupportRaw_sound`. (This is why these differ from `mem_certDepsList` /
`mem_certDepsDis`, which get their recursion from a `HasSupport` derivation
they can induct on and so can stay index-only.) -/
mutual
  theorem mem_usedBackends_occ (w : SupportTerm) (β : BackendId)
      (h : β ∈ usedBackends w) :
      ∃ o : CertOccurrence, OccursIn w o ∧ o.β = β := by
    cases w with
    | leaf l => simp [usedBackends] at h
    | inst rn θ ws D H α =>
      simp only [usedBackends] at h
      rcases List.mem_append.mp h with hroot | hD
      · rcases List.mem_append.mp hroot with hα | hws
        · cases α with
          | none => simp at hα
          | trusted => simp at hα
          | cert β' hd κ =>
            have hb : β = β' := by simpa using hα
            exact ⟨⟨rn, θ, ws, D, H, β', hd, κ⟩, .here, hb.symm⟩
        · obtain ⟨i, w', o, hw', ho, hβ⟩ := mem_usedBackendsListOcc ws β hws
          exact ⟨o, .prem hw' ho, hβ⟩
      · obtain ⟨j, q, w', o, hw', ho, hβ⟩ := mem_usedBackendsDisOcc D β hD
        exact ⟨o, .dis hw' ho, hβ⟩

  theorem mem_usedBackendsListOcc (ws : List SupportTerm) (β : BackendId)
      (h : β ∈ usedBackendsList ws) :
      ∃ (i : Nat) (w : SupportTerm) (o : CertOccurrence),
        ws[i]? = some w ∧ OccursIn w o ∧ o.β = β := by
    cases ws with
    | nil => simp [usedBackendsList] at h
    | cons w ws =>
      simp only [usedBackendsList] at h
      rcases List.mem_append.mp h with h1 | h2
      · obtain ⟨o, ho, hβ⟩ := mem_usedBackends_occ w β h1
        exact ⟨0, w, o, by simp, ho, hβ⟩
      · obtain ⟨i, w', o, hw', ho, hβ⟩ := mem_usedBackendsListOcc ws β h2
        exact ⟨i + 1, w', o, by simpa using hw', ho, hβ⟩

  theorem mem_usedBackendsDisOcc (D : List (QuestionId × SupportTerm))
      (β : BackendId) (h : β ∈ usedBackendsDis D) :
      ∃ (j : Nat) (q : QuestionId) (w : SupportTerm) (o : CertOccurrence),
        D[j]? = some (q, w) ∧ OccursIn w o ∧ o.β = β := by
    cases D with
    | nil => simp [usedBackendsDis] at h
    | cons qw rest =>
      obtain ⟨q, w⟩ := qw
      simp only [usedBackendsDis] at h
      rcases List.mem_append.mp h with h1 | h2
      · obtain ⟨o, ho, hβ⟩ := mem_usedBackends_occ w β h1
        exact ⟨0, q, w, o, by simp, ho, hβ⟩
      · obtain ⟨j, q', w', o, hw', ho, hβ⟩ := mem_usedBackendsDisOcc rest β h2
        exact ⟨j + 1, q', w', o, by simpa using hw', ho, hβ⟩
end

/-- **`usedBackends` is exactly the set of identities the term's certificate
occurrences name.** Neither over- nor under-approximate: a syntactic scan of
the term and the semantic notion "some occurrence uses `β`" agree. This is what
licenses stating heterogeneity as a property of `usedBackends w` while proving
it by induction on occurrences. -/
theorem mem_usedBackends_iff {w : SupportTerm} {β : BackendId} :
    β ∈ usedBackends w ↔ ∃ o : CertOccurrence, OccursIn w o ∧ o.β = β := by
  refine ⟨mem_usedBackends_occ w β, ?_⟩
  rintro ⟨o, ho, rfl⟩
  exact certStep_usedBackends_subset ho o.β (usedBackends_node o)

/-! ### The backend firewall: a typed subterm may be swapped for any other of
the same conclusion -/

/-- Rewriting one discharge subterm leaves the discharge *keys* untouched: the
pair `List.set` writes carries the same question `q` the pair it overwrites did.
This is the only lemma the discharge half of the firewall needs beyond lengths,
because the four `InstSide` fields that read the discharge *keys* — `dNodup`,
`cover`, `disj`, `keysD` — read them through `D.map Prod.fst`.

Two further fields do inspect `D` structurally without going through that
projection, and neither is discharged by this lemma: `ans` reads `D[j]?`
directly but constrains only the *answer atom* `DCs[j]`, which the swap leaves
untouched, and `strictNoQ` asserts `D = []` directly, where the swap is a
no-op. `dis_subterm_swap` below discharges both as separate cases. -/
theorem map_fst_set_of_getElem? {D : List (QuestionId × SupportTerm)} {j : Nat}
    {q : QuestionId} {w w' : SupportTerm} (hj : D[j]? = some (q, w)) :
    (D.set j (q, w')).map Prod.fst = D.map Prod.fst := by
  have hlt : j < (D.map Prod.fst).length := by
    simpa using lt_of_getElem?_some hj
  have hkey : (D.map Prod.fst)[j]? = some q := by
    simp [List.getElem?_map, hj]
  rw [List.map_set]
  refine List.ext_getElem? (fun k => ?_)
  by_cases hjk : j = k
  · subst hjk
    rw [List.getElem?_set_self hlt]
    exact hkey.symm
  · rw [List.getElem?_set_ne hjk]

/-- **The backend firewall (premise half).** A premise subterm may be replaced
by *any* term carrying the same conclusion and the same obligations, and the
parent instance stays typed at the same conclusion and the same obligation set.

The statement never mentions backends, and that is exactly its content: the
replacement is free to be certified by a different registered identity, over a
different private formula type, under a different theory — none of which the
statement can distinguish, because no side condition of the parent can express
the difference. `InstSide` reaches `ws` through three fields and all three are
lengths (`lenAs`, `lenCs`, `lenOs`); everything else the parent knows about a
premise arrives through `Cs` — the premise conclusions — and `premEq`, which
compares those to the instantiated patterns only up to `≡`. Since
`List.set` preserves length, the swap costs exactly three rewrites.

Naming the two backends is a corollary, not the theorem: the composition is
free because there is nothing here to relate. -/
theorem prem_subterm_swap {canon : String → String} {Pi : RuleId → Option Rule}
    {Gamma : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    {rn : RuleId} {θ : Subst} {ws : List SupportTerm}
    {D : List (QuestionId × SupportTerm)} {H : List QuestionId} {α : Assurance}
    {r : Rule} {As Cs : List Atom} {Os : List (List QuestionId)}
    {DCs : List Atom} {DOs : List (List QuestionId)} {C : Atom}
    (hside : InstSide canon Pi CertOk rn θ r ws D H α As Cs Os DCs DOs C)
    (hprems : ∀ (i : Nat) (w : SupportTerm) (A : Atom) (O : List QuestionId),
      ws[i]? = some w → Cs[i]? = some A → Os[i]? = some O →
      HasSupport canon Pi Gamma CertOk w A O)
    (hdis : ∀ (j : Nat) (q : QuestionId) (w : SupportTerm) (A : Atom)
      (O : List QuestionId), D[j]? = some (q, w) → DCs[j]? = some A →
      DOs[j]? = some O → HasSupport canon Pi Gamma CertOk w A O)
    {i : Nat} {w' : SupportTerm} {A' : Atom} {O' : List QuestionId}
    (hA : Cs[i]? = some A') (hO : Os[i]? = some O')
    (h' : HasSupport canon Pi Gamma CertOk w' A' O') :
    HasSupport canon Pi Gamma CertOk (.inst rn θ (ws.set i w') D H α) C
      (collectObligations Os DOs r H) := by
  refine .inst { hside with
      lenAs := by rw [List.length_set]; exact hside.lenAs
      lenCs := by rw [List.length_set]; exact hside.lenCs
      lenOs := by rw [List.length_set]; exact hside.lenOs }
    ?_ hdis
  intro k wk Ak Ok hk hAk hOk
  by_cases hik : i = k
  · subst hik
    by_cases hlt : i < ws.length
    · -- the swapped slot: its premise obligation is discharged by `h'`, whose
      -- conclusion and obligations are the ones the parent already recorded
      rw [List.getElem?_set_self hlt] at hk
      obtain rfl : w' = wk := Option.some.inj hk
      obtain rfl : Ak = A' := Option.some.inj (hAk.symm.trans hA)
      obtain rfl : Ok = O' := Option.some.inj (hOk.symm.trans hO)
      exact h'
    · -- out of range: `List.set` was a no-op, so the original premise stands
      rw [List.set_eq_of_length_le (Nat.le_of_not_lt hlt)] at hk
      exact hprems i wk Ak Ok hk hAk hOk
  · rw [List.getElem?_set_ne hik] at hk
    exact hprems k wk Ak Ok hk hAk hOk

/-- **The backend firewall (discharge half).** The same swap at a discharge
slot: replacing `D[j] = (q, w)` by `(q, w')` for any `w'` with the same
conclusion and obligations preserves the parent's typing, again without the
statement mentioning a backend.

More of `InstSide` moves here than in the premise case, so the surviving side
conditions are written out one by one rather than inherited with `{ hside with
… }` — the point of the theorem is *which* fields survive the swap and why:

* `lenDCs`/`lenDOs` are lengths, and `List.set` preserves length;
* `dNodup`, `cover`, `disj` and `keysD` read `D` only through
  `D.map Prod.fst`, which `map_fst_set_of_getElem?` shows is unchanged — the
  question key `q` is deliberately carried over from the old pair;
* `ans` constrains the *answer atom* `DCs[j]` against the question's pattern,
  and `DCs` is untouched; it quantifies over the discharge term but its
  conclusion never mentions it;
* `strictNoQ` only ever fires when `D = []`, where the swap is a no-op;
* every remaining field — the rule lookup, `θ`, the premise side, the
  assurance — does not mention `D` at all.

Nothing in that list can see the replacement's assurance. -/
theorem dis_subterm_swap {canon : String → String} {Pi : RuleId → Option Rule}
    {Gamma : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    {rn : RuleId} {θ : Subst} {ws : List SupportTerm}
    {D : List (QuestionId × SupportTerm)} {H : List QuestionId} {α : Assurance}
    {r : Rule} {As Cs : List Atom} {Os : List (List QuestionId)}
    {DCs : List Atom} {DOs : List (List QuestionId)} {C : Atom}
    (hside : InstSide canon Pi CertOk rn θ r ws D H α As Cs Os DCs DOs C)
    (hprems : ∀ (i : Nat) (w : SupportTerm) (A : Atom) (O : List QuestionId),
      ws[i]? = some w → Cs[i]? = some A → Os[i]? = some O →
      HasSupport canon Pi Gamma CertOk w A O)
    (hdis : ∀ (j : Nat) (q : QuestionId) (w : SupportTerm) (A : Atom)
      (O : List QuestionId), D[j]? = some (q, w) → DCs[j]? = some A →
      DOs[j]? = some O → HasSupport canon Pi Gamma CertOk w A O)
    {j : Nat} {q : QuestionId} {w w' : SupportTerm} {A' : Atom}
    {O' : List QuestionId}
    (hqw : D[j]? = some (q, w)) (hA : DCs[j]? = some A') (hO : DOs[j]? = some O')
    (h' : HasSupport canon Pi Gamma CertOk w' A' O') :
    HasSupport canon Pi Gamma CertOk (.inst rn θ ws (D.set j (q, w')) H α) C
      (collectObligations Os DOs r H) := by
  have hjlt : j < D.length := lt_of_getElem?_some hqw
  have hkeys : (D.set j (q, w')).map Prod.fst = D.map Prod.fst :=
    map_fst_set_of_getElem? hqw
  -- Every slot of the rewritten map still names a question the original had,
  -- at the same index — the only fact `ans` and `hdis` need to transfer.
  have hback : ∀ (k : Nat) (q₀ : QuestionId) (u : SupportTerm),
      (D.set j (q, w'))[k]? = some (q₀, u) → ∃ u₀, D[k]? = some (q₀, u₀) := by
    intro k q₀ u hk
    by_cases hjk : j = k
    · subst hjk
      rw [List.getElem?_set_self hjlt] at hk
      obtain ⟨rfl, -⟩ : q = q₀ ∧ w' = u := by simpa using hk
      exact ⟨w, hqw⟩
    · rw [List.getElem?_set_ne hjk] at hk
      exact ⟨u, hk⟩
  refine .inst
    { rule      := hside.rule
      θNodup    := hside.θNodup
      θDom      := hside.θDom
      prems     := hside.prems
      concl     := hside.concl
      lenAs     := hside.lenAs
      lenCs     := hside.lenCs
      lenOs     := hside.lenOs
      premEq    := hside.premEq
      lenDCs    := by rw [List.length_set]; exact hside.lenDCs
      lenDOs    := by rw [List.length_set]; exact hside.lenDOs
      ans       := fun k q₀ u A hk hAk =>
        let ⟨u₀, hu₀⟩ := hback k q₀ u hk
        hside.ans k q₀ u₀ A hu₀ hAk
      qNodup    := hside.qNodup
      dNodup    := by rw [hkeys]; exact hside.dNodup
      hNodup    := hside.hNodup
      cover     := by rw [hkeys]; exact hside.cover
      disj      := by rw [hkeys]; exact hside.disj
      keysD     := by rw [hkeys]; exact hside.keysD
      keysH     := hside.keysH
      strictNoQ := by
        intro hm
        obtain ⟨hD, hH⟩ := hside.strictNoQ hm
        exact ⟨by rw [hD]; simp, hH⟩
      assur     := hside.assur }
    hprems ?_
  intro k q₀ u A O hk hAk hOk
  by_cases hjk : j = k
  · subst hjk
    -- the swapped slot: `h'` is the replacement's derivation, and the answer
    -- atom and obligations the parent recorded are unchanged
    rw [List.getElem?_set_self hjlt] at hk
    obtain ⟨-, rfl⟩ : q = q₀ ∧ w' = u := by simpa using hk
    obtain rfl : A = A' := Option.some.inj (hAk.symm.trans hA)
    obtain rfl : O = O' := Option.some.inj (hOk.symm.trans hO)
    exact h'
  · rw [List.getElem?_set_ne hjk] at hk
    exact hdis k q₀ u A O hk hAk hOk

/-! ### Accounting, restated over occurrences -/

/-- Only a certificate node reports anything, so membership in a node's report
determines the node's shape.

This is the inversion that lets an occurrence-indexed statement consume a
node-indexed one. `mem_certDeps_step` (`Lara/Support.lean`) hands back a bare
`u : SupportTerm` together with `d ∈ stepDeps Pi reg u`; to name that `u` as a
`CertOccurrence` we need to know it is an `.inst` carrying an `Assurance.cert`.
`stepDeps` answers `[]` on every other shape — a leaf, a defeasible instance, a
trusted instance — so the membership hypothesis is itself the evidence, and no
typing derivation is needed. -/
theorem stepDeps_cert_shape {canon : String → String} {Pi : RuleId → Option Rule}
    {reg : BackendRegistry canon} {u : SupportTerm} {d : CertDep}
    (hmem : d ∈ stepDeps Pi reg u) : ∃ o : CertOccurrence, u = o.node := by
  cases u with
  | leaf _ => simp [stepDeps] at hmem
  | inst rn θ ws D H α =>
    cases α with
    | none => simp [stepDeps] at hmem
    | trusted => simp [stepDeps] at hmem
    | cert β hdg κ => exact ⟨⟨rn, θ, ws, D, H, β, hdg, κ⟩, rfl⟩

/-- **Certificate dependencies are exactly the union of the occurrence-local
backend reports.** `mem_certDeps_step` and `certStep_deps_subset`
(`Lara/Support.lean`) as a single iff over occurrences.

Each `stepDeps o.node` is computed by `o.β`'s *own* core — `stepDeps` looks up
`reg o.β`, resolves `o.hd` through that record, and maps `registered.core.uses`
over the slots — so the right-hand side is a union over heterogeneous
reporters, not a report from a shared one. Two occurrences with different
identities contribute entries computed by different cores, and `certDeps`
merely concatenates them; nothing in the statement or its proof relates the two
computations. That is why the collection law survives heterogeneity unchanged:
it never had to look inside a backend to hold. -/
theorem certDeps_eq_union {canon Pi Gamma} {reg : BackendRegistry canon}
    {w : SupportTerm} {C : Atom} {O : List QuestionId}
    (h : HasSupport canon Pi Gamma (certOkOf reg) w C O) (d : CertDep) :
    d ∈ certDeps Pi reg w ↔
      ∃ o : CertOccurrence, OccursIn w o ∧ d ∈ stepDeps Pi reg o.node := by
  refine ⟨fun hmem => ?_, ?_⟩
  · obtain ⟨u, hu, hstep⟩ := mem_certDeps_step h d hmem
    obtain ⟨o, rfl⟩ := stepDeps_cert_shape hstep
    exact ⟨o, hu, hstep⟩
  · rintro ⟨o, ho, hstep⟩
    exact certStep_deps_subset ho d hstep

/-- **B0 headline.** Every certified occurrence of a typed term is accounted by
*its own* registered core: the backend record, its private formula type, and its
resolved theory are bound inside the per-occurrence existential
(`OccurrenceConsequence`). No binder in scope requires occurrences with
different identities to share a formula type, theory data, or consequence
relation, and the term is well-typed regardless — there is no shared backend
logic to introduce, because there is no binder in scope that could relate two
occurrences.

The conjunction is the paper's target verbatim: the occurrence's rule is strict
and allowlists `(β, hd)`, its premises and conclusion instantiate, **its local
checker accepts its certificate** (`certOkOf reg o.β o.hd o.κ As Cn`), and its
backend's own consequence relation delivers the conclusion from the reported
slots. Acceptance and consequence are separate conjuncts on purpose:
acceptance is the *checkable* fact a verifier re-runs, consequence is the
*semantic* fact it buys, and `certOkOf_uses_account` is what connects them.

Derivation, not re-proof (design decision D4): the last conjunct is
`cert_steps_accounted` regrouped through `OccurrenceConsequence`, and the
acceptance conjunct is one `AssuranceOk` inversion on the node's own typing
derivation, obtained from `certStepIn_typed`. Both derivations name a rule, an
instantiated premise list, and a conclusion independently; they are identified
here by `Option` injectivity on the shared lookups `Pi o.rn`,
`instAPats o.θ r.premises`, `instAPat o.θ r.concl`, which is the only real work
in the proof. -/
theorem hetero_occurrences_accounted {canon Pi Gamma} {reg : BackendRegistry canon}
    {w : SupportTerm} {C : Atom} {O : List QuestionId}
    (h : HasSupport canon Pi Gamma (certOkOf reg) w C O) :
    ∀ o : CertOccurrence, OccursIn w o →
      ∃ r As Cn, Pi o.rn = some r ∧ r.mode = .strict ∧
        (o.β, o.hd) ∈ r.certifiers ∧
        instAPats o.θ r.premises = some As ∧ instAPat o.θ r.concl = some Cn ∧
        certOkOf reg o.β o.hd o.κ As Cn ∧
        OccurrenceConsequence reg o.β o.hd o.κ As Cn := by
  intro o ho
  -- the consequence half: `cert_steps_accounted` applied at the occurrence's
  -- eight fields, which is exactly its eight-binder node pattern
  obtain ⟨r, As, Cn, registered, T, hr, hm, hallow, hAs, hCn, hreg, hres,
    hmodels⟩ := cert_steps_accounted h o.rn o.θ o.ws o.D o.H o.β o.hd o.κ ho
  refine ⟨r, As, Cn, hr, hm, hallow, hAs, hCn, ?_, registered, T, hreg, hres,
    hmodels⟩
  -- the acceptance half: the occurring node is itself typed, and its
  -- `InstSide` carries an `AssuranceOk` whose `cert` case *is* the acceptance
  obtain ⟨C', O', h'⟩ := certStepIn_typed h _ ho
  have hnode : HasSupport canon Pi Gamma (certOkOf reg)
      (.inst o.rn o.θ o.ws o.D o.H (.cert o.β o.hd o.κ)) C' O' := h'
  cases hnode with
  | @inst _ _ _ _ _ _ r' As' Cs Os DCs DOs _ hside hprems hdis =>
    cases hside.assur with
    | cert _ _ hacc =>
      -- this inversion picked its own rule, premises and conclusion; they are
      -- the ones `cert_steps_accounted` picked, because both are values of the
      -- same three partial lookups at the same arguments
      obtain rfl : r' = r := Option.some.inj (hside.rule.symm.trans hr)
      obtain rfl : As' = As := Option.some.inj (hside.prems.symm.trans hAs)
      obtain rfl : C' = Cn := Option.some.inj (hside.concl.symm.trans hCn)
      exact hacc

/-- **Every backend a typed term *names* is registered and discharges an
occurrence in its own logic.** `mem_usedBackends_iff` composed with
`hetero_occurrences_accounted`: the syntactic identity list is exactly the set
of logics the term's correctness actually rests on — no name in `usedBackends w`
is decorative, and no logic the term depends on is missing from it.

The conclusion carries the occurrence *and* its discharge, not merely
registration: registration (`reg β = some registered`) is a projection of
`OccurrenceConsequence`, so a statement that stopped there would be strictly
weaker than what the derivation already provides. Reading it as an audit: for
each `β` a reviewer scans out of the term, this names the occurrence to inspect,
the certificate `o.κ` to re-check against `β`'s own checker, and the theory
digest `o.hd` that fixes which axioms that check may consult. -/
theorem usedBackends_accounted {canon Pi Gamma} {reg : BackendRegistry canon}
    {w : SupportTerm} {C : Atom} {O : List QuestionId}
    (h : HasSupport canon Pi Gamma (certOkOf reg) w C O) :
    ∀ β ∈ usedBackends w, ∃ o : CertOccurrence, OccursIn w o ∧ o.β = β ∧
      ∃ As Cn, certOkOf reg β o.hd o.κ As Cn ∧
        OccurrenceConsequence reg β o.hd o.κ As Cn := by
  intro β hβ
  obtain ⟨o, ho, rfl⟩ := mem_usedBackends_iff.mp hβ
  obtain ⟨_, As, Cn, _, _, _, _, _, hacc, hcons⟩ :=
    hetero_occurrences_accounted h o ho
  exact ⟨o, ho, rfl, As, Cn, hacc, hcons⟩

end Lara.BackendComposition
