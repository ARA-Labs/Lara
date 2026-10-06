/-
Duplicate-world identity in the `pw-run 1` loader carries located holes.

One context, three worlds, loaded with the loader's own `extendCtx` under the
production canonicalizer, leaf context and registry. `w0` declares the
complete argument `leaf l1`. `w1` declares the same complete argument and the
hole `tMix`, which leaves the mandatory `q1` open. Their checked programs have
equal AF arguments and equal compiled attacks and differ only in their located
holes, so the loader keeps both (`holes_world_kept`); under an identity of
arguments and attacks alone the two would coincide
(`holes_world_complete_parts_agree`). `w2` declares `w1`'s arguments in the
other order: its checked program, holes included, is `w1`'s, and the loader
refuses it as a duplicate state (`holes_world_duplicate`).

Each cell is one kernel `decide` (`decide +kernel`): the elaborator's
`decide` runs out of heartbeats evaluating the checker under the production
canonicalizer, while the kernel checks each cell directly. `native_decide` is
not used.
-/
import Lara.PW.Run
import Lara.Examples

namespace Lara.Examples.PWRun

open Lara.Support Lara.PW.Run Lara.Examples

/-- The shared environment: the example signature and policy (whose `rmix`
has the mandatory question `q1`), and the example leaves. -/
def envHoles : Env :=
  ⟨sigmaEx, unitPolicyEx, [(l1, pA), (l2, pB), (l3, pC)], []⟩

def ctxEmpty : LoadedCtx := ⟨⟨"c"⟩, envHoles, [], List.nodup_nil⟩

/-- `w0`: the complete argument alone. -/
def loadW0 : Except WorldError LoadedCtx :=
  extendCtx ctxEmpty ⟨"w0"⟩ groundEx [.leaf l1] []

/-- `w1`: the same complete argument beside the hole `tMix`. -/
def loadW1 : Except WorldError LoadedCtx :=
  loadW0 >>= fun c => extendCtx c ⟨"w1"⟩ groundEx [.leaf l1, tMix] []

/-- `w2`: `w1`'s declarations, reordered. -/
def loadW2 : Except WorldError LoadedCtx :=
  loadW1 >>= fun c => extendCtx c ⟨"w2"⟩ groundEx [tMix, .leaf l1] []

/-- The duplicate-state refusal a load ended in, if any. -/
def duplicateOf : Except WorldError LoadedCtx → Option (WorldId × WorldId)
  | .error (.duplicateState w earlier) => some (w, earlier)
  | _ => none

/-- Both worlds are loaded, in declaration order. -/
theorem holes_world_kept :
    loadW1.toOption.map (fun c => c.worlds.map (·.id)) =
      some [⟨"w0"⟩, ⟨"w1"⟩] := by
  decide +kernel

/-- The two states differ exactly in the hole ledger. -/
theorem holes_world_states :
    loadW1.toOption.map (fun c => c.worlds.map (·.state)) =
      some [([.leaf l1], [], []), ([.leaf l1], [], [tMix])] := by
  decide +kernel

/-- Arguments and attacks alone do not tell the two worlds apart. -/
theorem holes_world_complete_parts_agree :
    loadW1.toOption.map (fun c => c.worlds.map fun w => (w.state.1, w.state.2.1)) =
      some [([.leaf l1], []), ([.leaf l1], [])] := by
  decide +kernel

/-- Repeating a checked program, holes included, is still a duplicate state. -/
theorem holes_world_duplicate :
    duplicateOf loadW2 = some (⟨"w2"⟩, ⟨"w1"⟩) := by
  decide +kernel

end Lara.Examples.PWRun
