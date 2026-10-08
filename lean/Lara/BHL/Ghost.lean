import Lara.BHL.ModelLaws

/-!
Intrinsically scoped ghost bindings over actual mathematical values. Contexts
contain only sorts; environments and renamings are semantic maps, not fields of
an assertion or term syntax. Renaming composition applies its first argument
before its second, and environment reindexing pulls a target environment back.
-/

namespace Lara.BHL

/-- Closed ghost sorts, including mathematical datasets, worlds, and finite traces. -/
inductive GhostSort where
  | value : ValueSort → GhostSort
  | dataset
  | world
  | trace
  deriving DecidableEq

/-- Ghosts denote values directly, without memory undefinedness or ambient traces. -/
abbrev GhostValue (D Command : Type) : GhostSort → Type
  | .value sort => Value sort
  | .dataset => D
  | .world => World D Command
  | .trace => List (State D Command)

/-- A sorted de Bruijn index can only refer to a binder in its own context. -/
inductive BoundGhost : List GhostSort → GhostSort → Type where
  | here {ctx : List GhostSort} {sort : GhostSort} : BoundGhost (sort :: ctx) sort
  | there {ctx : List GhostSort} {sort other : GhostSort} :
      BoundGhost ctx sort → BoundGhost (other :: ctx) sort

/-- A semantic environment assigns an actual value to each intrinsically sorted index. -/
abbrev GhostEnv (D Command : Type) (ctx : List GhostSort) :=
  (sort : GhostSort) → BoundGhost ctx sort → GhostValue D Command sort

/-- A renaming preserves sorts while changing the context of bound indices. -/
abbrev GhostRenaming (ctx target : List GhostSort) :=
  (sort : GhostSort) → BoundGhost ctx sort → BoundGhost target sort

namespace GhostRenaming

variable {ctx target next last : List GhostSort} {sort other : GhostSort}

/-- The identity leaves every bound index unchanged. -/
def id : GhostRenaming ctx ctx := fun _ index => index

/-- Apply the source-to-target map first, then the target-to-next map. -/
def comp (ρ : GhostRenaming ctx target) (σ : GhostRenaming target next) :
    GhostRenaming ctx next :=
  fun sort index => σ sort (ρ sort index)

/-- Introduce one fresh binder without capturing any old index. -/
def weaken : GhostRenaming ctx (other :: ctx) := fun _ index => .there index

/-- Preserve the fresh binder and rename only indices from the old context. -/
def lift (ρ : GhostRenaming ctx target) : GhostRenaming (other :: ctx) (other :: target)
  | _, .here => .here
  | _, .there index => .there (ρ _ index)

@[simp] theorem id_apply (index : BoundGhost ctx sort) : id sort index = index := rfl

@[simp] theorem comp_apply (ρ : GhostRenaming ctx target) (σ : GhostRenaming target next)
    (index : BoundGhost ctx sort) :
    comp ρ σ sort index = σ sort (ρ sort index) := rfl

@[simp] theorem weaken_apply (index : BoundGhost ctx sort) :
    weaken (other := other) sort index = .there index := rfl

@[simp] theorem lift_here (ρ : GhostRenaming ctx target) :
    lift (other := other) ρ other .here = .here := rfl

@[simp] theorem lift_there (ρ : GhostRenaming ctx target) (index : BoundGhost ctx sort) :
    lift (other := other) ρ sort (.there index) = .there (ρ sort index) := rfl

@[simp] theorem id_comp (ρ : GhostRenaming ctx target) : comp id ρ = ρ := rfl

@[simp] theorem comp_id (ρ : GhostRenaming ctx target) : comp ρ id = ρ := rfl

 theorem comp_assoc (ρ : GhostRenaming ctx target) (σ : GhostRenaming target next)
    (τ : GhostRenaming next last) : comp (comp ρ σ) τ = comp ρ (comp σ τ) := rfl

@[simp] theorem lift_id : lift (other := other) (id (ctx := ctx)) = id := by
  funext sort index
  cases index <;> rfl

 theorem lift_comp (ρ : GhostRenaming ctx target) (σ : GhostRenaming target next) :
    lift (other := other) (comp ρ σ) = comp (lift ρ) (lift σ) := by
  funext sort index
  cases index <;> rfl

/-- Weakening commutes with a renaming lifted across the same fresh binder. -/
 theorem weaken_comp_lift (ρ : GhostRenaming ctx target) :
    comp (weaken (other := other)) (lift ρ) = comp ρ weaken := rfl

end GhostRenaming

namespace GhostEnv

variable {D Command : Type} {ctx target next : List GhostSort} {sort other : GhostSort}

/-- There are no indices to interpret in the empty context. -/
def empty : GhostEnv D Command [] := fun _ index => nomatch index

/-- Extend an environment by one typed mathematical value. -/
def push (value : GhostValue D Command sort) (env : GhostEnv D Command ctx) :
    GhostEnv D Command (sort :: ctx)
  | _, .here => value
  | _, .there index => env _ index

/-- Interpret a bound index without an untyped lookup or a failure case. -/
def lookup (env : GhostEnv D Command ctx) (index : BoundGhost ctx sort) :
    GhostValue D Command sort :=
  env sort index

/-- Pull a target environment back along a sorted renaming. -/
def reindex (ρ : GhostRenaming ctx target) (env : GhostEnv D Command target) :
    GhostEnv D Command ctx :=
  fun sort index => env sort (ρ sort index)

@[simp] theorem lookup_push_here (value : GhostValue D Command sort)
    (env : GhostEnv D Command ctx) : lookup (push value env) .here = value := rfl

@[simp] theorem lookup_push_there (value : GhostValue D Command other)
    (env : GhostEnv D Command ctx) (index : BoundGhost ctx sort) :
    lookup (push value env) (.there index) = lookup env index := rfl

@[ext] theorem ext {left right : GhostEnv D Command ctx}
    (h : ∀ (sort : GhostSort) (index : BoundGhost ctx sort),
      lookup left index = lookup right index) : left = right :=
  funext fun sort => funext fun index => h sort index

 theorem empty_unique (env : GhostEnv D Command []) : env = empty := by
  apply ext
  intro sort index
  cases index

@[simp] theorem lookup_reindex (ρ : GhostRenaming ctx target)
    (env : GhostEnv D Command target) (index : BoundGhost ctx sort) :
    lookup (reindex ρ env) index = lookup env (ρ sort index) := rfl

@[simp] theorem reindex_id (env : GhostEnv D Command ctx) :
    reindex GhostRenaming.id env = env := rfl

 theorem reindex_comp (ρ : GhostRenaming ctx target) (σ : GhostRenaming target next)
    (env : GhostEnv D Command next) :
    reindex (GhostRenaming.comp ρ σ) env = reindex ρ (reindex σ env) := rfl

/-- The new value disappears when the environment is restricted to its old indices. -/
@[simp] theorem reindex_weaken_push (value : GhostValue D Command other)
    (env : GhostEnv D Command ctx) :
    reindex GhostRenaming.weaken (push value env) = env := rfl

/-- A lifted renaming preserves the new value and reindexes only the old environment. -/
@[simp] theorem reindex_lift_push (ρ : GhostRenaming ctx target)
    (value : GhostValue D Command other) (env : GhostEnv D Command target) :
    reindex (GhostRenaming.lift ρ) (push value env) = push value (reindex ρ env) := by
  apply ext
  intro sort index
  cases index <;> rfl

/-- Every nonempty environment is its head value pushed onto its restriction. -/
 theorem push_lookup_reindex (env : GhostEnv D Command (other :: ctx)) :
    push (lookup env (.here : BoundGhost (other :: ctx) other))
      (reindex GhostRenaming.weaken env) = env := by
  apply ext
  intro sort index
  cases index <;> rfl

/-- Two extended environments agree exactly when their head and tail agree. -/
 theorem push_eq_push_iff (leftValue rightValue : GhostValue D Command other)
    (left right : GhostEnv D Command ctx) :
    push leftValue left = push rightValue right ↔ leftValue = rightValue ∧ left = right := by
  constructor
  · intro h
    constructor
    · exact congrArg (fun env : GhostEnv D Command (other :: ctx) =>
        lookup env (.here : BoundGhost (other :: ctx) other)) h
    · exact congrArg (fun env : GhostEnv D Command (other :: ctx) =>
        reindex (GhostRenaming.weaken (ctx := ctx) (other := other)) env) h
  · rintro ⟨rfl, rfl⟩
    rfl

end GhostEnv

end Lara.BHL
