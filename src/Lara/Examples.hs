-- | Concrete LARA abstract-syntax examples (spec §10 asks for at least three
-- complete real examples).
--
-- Every program here is a hand-built 'Program' value over the "Lara.AST"
-- placeholder types. The claims, evidence, and defeats are transcribed from the
-- real research artifacts in the ARA-Demo corpus
-- (<https://github.com/ARA-Labs/ARA-Demo>), so the shapes are what an untrusted
-- ARA elaborator (spec §11) would actually have to produce:
--
--   * 'nanogptTailEma'  — nanoGPT-speedrun claim C02 (tail-EMA is the strongest
--     v1 ablation lever): a defeasible ablation argument with one discharged and
--     one open critical question. This is the spec §10 "intentionally
--     incomplete, reports a located obligation" pattern on a real claim.
--   * 'nanogptV12Quarantine' — claim C05 (an illegal forward-path precision
--     change materially helped and was quarantined): a claim whose support is
--     __defeated__ by an undermine on the leaf it rests on. Demonstrates
--     non-monotonic retraction (spec §8) driven by a compliance attack.
--   * 'ls20SwitchDispute' — ARC-AGI-3 ls20 claims C08 vs C09 (the "hidden second
--     control" hypothesis vs "one 4-state-cycle switch suffices"): two
--     mutually-contrary defeasible arguments with a 'Rebut', the shape a refuted
--     hypothesis takes once a live solve contradicts it.
--
-- These are __data only__: there is no checker yet ("Lara.AST" documents that),
-- so nothing here is validated, compiled to a Dung framework, or labelled. The
-- 'exampleStatus' notes record the status each example is /designed/ to report
-- once the checker exists, matching the source claim's real disposition.
module Lara.Examples
  ( -- * Examples
    nanogptTailEma
  , nanogptV12Quarantine
  , ls20SwitchDispute
    -- * Index
  , allExamples
  ) where

import Lara.AST
import Lara.Prop (Prop (..), Term (..))

-- ---------------------------------------------------------------------------
-- Small construction helpers (presentation-syntax sugar in Haskell)
-- ---------------------------------------------------------------------------

-- | A nullary-constructor ground term (an identifier constant like @tailEMA@).
con :: String -> Term
con k = TCon (FunSym k) []

-- | A constructor applied to arguments, e.g. @top_delta(tailEMA, +0.00251)@.
funT :: String -> [Term] -> Term
funT k = TCon (FunSym k)

-- | An atomic proposition @pred(g1, …, gn)@.
atom :: String -> [Term] -> Prop
atom p = Prop (Pred p)

-- | A leaf supporting itself as evidence, with kind and provenance.
leaf :: String -> Prop -> LeafKind -> Provenance -> [String] -> Leaf
leaf lid p k prov refs =
  Leaf
    { leafId = LeafId lid
    , leafProp = p
    , leafKind = k
    , leafProvenance = prov
    , leafRefs = map SourceRef refs
    }

-- | A defeasible rule instance with premises, discharge map, and holes.
inst
  :: String
  -> Subst
  -> [SupportTerm]
  -> [(QuestionId, SupportTerm)]
  -> [ObligationId]
  -> SupportTerm
inst r theta prems disch holes =
  SRule
    { srRule = RuleId r
    , srSubst = theta
    , srPremises = prems
    , srDischarge = disch
    , srHoles = holes
    , srAssurance = AssuranceNone
    }

-- ===========================================================================
-- Example 1 — nanoGPT C02: tail-EMA is the strongest v1 ablation lever
-- ===========================================================================

-- | nanoGPT-speedrun claim __C02__: "Tail-EMA evaluation is the single strongest
-- endpoint-smoothing lever in the v1 stack."
--
-- ARA source:
-- <https://github.com/ARA-Labs/ARA-Demo/blob/main/nanogpt_ara/logic/claims.md#L46-L74>
--
-- Presentation syntax (spec §10 style):
--
-- > artifact nanogpt_ara at sha256:c02…
-- > policy empirical-ablation-v1
-- > use backends [nd@1]
-- >
-- > claim c02
-- >   nl      = "Tail-EMA evaluation is the single strongest endpoint-smoothing
-- >              lever in the v1 stack"
-- >   formal  = strongest_ablation_lever(tailEMA, v1_stack)
-- >   binding = { author = codex, audit-status = reviewed }
-- >
-- > leaf e_prune : reports(v1_pruning, top_delta(tailEMA, +0.00251))
-- >   kind = observed  provenance = ai-executed
-- >   refs = [record_configs/20260515_codex_v1_v12iso_3205/pruning_data.json#L111]
-- >
-- > arg a02 : supports(c02) by leave_one_out_ranking(e_prune) where component = tailEMA
-- >   discharge beats_next_lever with e_next     -- noMuon2f delta +0.00229 < +0.00251
-- >   open      seed_stability as o_seed         -- "seed-fragile below the stop floor" (C02 Conditions)
-- >
-- > status c02
--
-- Designed status: __gap__ — the mandatory @seed_stability@ question is left open
-- (@o_seed@), matching C02's own "seed-fragile below the practical stop floor"
-- caveat, so the argument is incomplete exactly as spec §10 intends.
nanogptTailEma :: Program
nanogptTailEma =
  Program
    { programArtifact = "nanogpt_ara"
    , programDigest = Digest "sha256:c02aab…"
    , programPolicy = PolicyId "empirical-ablation-v1"
    , programBackends = [(BackendId "nd", "1")]
    , programDecls =
        [ DeclClaim
            Claim
              { claimId = PropId "c02"
              , claimNl =
                  "Tail-EMA evaluation is the single strongest "
                    ++ "endpoint-smoothing lever in the v1 stack"
              , claimFormal = atom "strongest_ablation_lever" [con "tailEMA", con "v1_stack"]
              , claimBinding =
                  Binding
                    { bindingAuthor = "codex"
                    , bindingRationale = "largest positive val-loss delta at the v1 pruning step"
                    , bindingAuditStatus = Reviewed
                    }
              }
        , DeclLeaf $
            leaf
              "e_prune"
              (atom "reports" [con "v1_pruning", funT "top_delta" [con "tailEMA", TNum "+0.00251"]])
              Observed
              AiExecuted
              ["record_configs/20260515_codex_v1_v12iso_3205/pruning_data.json#L111"]
        , DeclLeaf $
            leaf
              "e_next"
              (atom "reports" [con "v1_pruning", funT "next_delta" [con "noMuon2f", TNum "+0.00229"]])
              Observed
              AiExecuted
              ["record_configs/20260515_codex_v1_v12iso_3205/pruning_data.json#L103"]
        , DeclArg
            Arg
              { argId = ArgId "a02"
              , argConcl = SupportsClaim (PropId "c02")
              , argTerm =
                  inst
                    "leave_one_out_ranking"
                    [(Param "Component", con "tailEMA"), (Param "Stack", con "v1_stack")]
                    [SLeaf (LeafId "e_prune")]
                    -- discharge: it beats the next-largest lever (noMuon2f)
                    [(QuestionId "beats_next_lever", SLeaf (LeafId "e_next"))]
                    -- open mandatory hole: seed stability is unshown (C02 caveat)
                    [ObligationId "o_seed"]
              }
        , DeclStatus (PropId "c02")
        ]
    }

-- ===========================================================================
-- Example 2 — nanoGPT C05: the quarantined illegal v12 forward-path change
-- ===========================================================================

-- | nanoGPT-speedrun claim __C05__: "an inherited 'v12' precision change was
-- illegal and materially helped, so it was quarantined." The sub-3000 frontier
-- built on it is __not a valid record__.
--
-- ARA source:
-- <https://github.com/ARA-Labs/ARA-Demo/blob/main/nanogpt_ara/logic/claims.md#L133-L163>
--
-- This is the defeat example. It is an __undercut__, not an undermine: the loss
-- crossing was genuinely observed (@e_loss@ is a real measurement, so attacking
-- it as false would misrepresent the epistemics, spec §4.2). What is broken is
-- the /inference/ from "crossed 3000" to "valid record" — the forward path was
-- illegally rewritten. The policy therefore declares
-- @exception record_from_crossing : forward_path_rewrite(C)@, and an argument
-- concluding @forward_path_rewrite(rmsnorm)@ undercuts exactly the record
-- instances whose @theta@ makes that the attacker's conclusion (spec §7).
--
-- Presentation syntax:
--
-- > policy empirical-ablation-v1
-- >   exception record_from_crossing : forward_path_rewrite(C)
-- >
-- > claim c05_record
-- >   nl      = "The v12-derived stack sets a valid sub-3000 record"
-- >   formal  = valid_record(v12_stack, bin_2962)
-- >   binding = { author = codex, audit-status = disputed }
-- >
-- > leaf e_loss  : reports(v12_stack, reached(bin_2962))                     kind=observed
-- > leaf e_audit : reports(compliance_audit, forward_path_rewrite(rmsnorm))  kind=attested prov=user
-- >
-- > arg a_rec  : supports(c05_record)                by record_from_crossing(e_loss)
-- > arg d_comp : supports(forward_path_rewrite(rmsnorm)) by forward_path_violation(e_audit)
-- >
-- > undercut d_comp a_rec.rule     -- the illegal forward path defeats the inference, not the datum
-- >
-- > status c05_record
--
-- Designed status: __defeated__ — the record argument's root rule occurrence is
-- undercut by the (user-provenance) compliance audit, so C05 is
-- "refuted-as-submittable / quarantined". Adding the checked attacker retracts a
-- status that would otherwise be @justified@ — the non-monotonicity of spec §8.
nanogptV12Quarantine :: Program
nanogptV12Quarantine =
  Program
    { programArtifact = "nanogpt_ara"
    , programDigest = Digest "sha256:c05dd…"
    , programPolicy = PolicyId "empirical-ablation-v1"
    , programBackends = [(BackendId "nd", "1")]
    , programDecls =
        [ DeclClaim
            Claim
              { claimId = PropId "c05_record"
              , claimNl = "The v12-derived stack sets a valid sub-3000 record"
              , claimFormal = atom "valid_record" [con "v12_stack", con "bin_2962"]
              , claimBinding =
                  Binding
                    { bindingAuthor = "codex"
                    , bindingRationale = "single-seed crossing below 3000 on the v12 parent"
                    , bindingAuditStatus = Disputed
                    }
              }
        , DeclLeaf $
            leaf
              "e_loss"
              (atom "reports" [con "v12_stack", funT "reached" [con "bin_2962"]])
              Observed
              AiExecuted
              ["v2/codex/scratchpad/THREAD.md#L120"]
        , -- The user-flagged compliance violation. Provenance = User: it is the
          -- human-signed audit that triggered the quarantine (C05 is user-revised).
          DeclLeaf $
            leaf
              "e_audit"
              (atom "reports" [con "compliance_audit", funT "forward_path_rewrite" [con "rmsnorm"]])
              Attested
              User
              ["v2/codex/scratchpad/THREAD.md#L126"]
        , DeclArg
            Arg
              { argId = ArgId "a_rec"
              , argConcl = SupportsClaim (PropId "c05_record")
              , argTerm =
                  inst
                    "record_from_crossing"
                    [(Param "Stack", con "v12_stack"), (Param "Bin", con "bin_2962")]
                    [SLeaf (LeafId "e_loss")]
                    []
                    []
              }
        , DeclArg
            Arg
              { argId = ArgId "d_comp"
              , -- c05_compliance is not a declared claim; its proposition
                -- (forward_path_rewrite(rmsnorm)) is derived from the term's conclusion.
                argConcl = SupportsDerived (PropId "c05_compliance")
              , argTerm =
                  inst
                    "forward_path_violation"
                    [(Param "Component", con "rmsnorm")]
                    [SLeaf (LeafId "e_audit")]
                    []
                    []
              }
        , -- undercut the record argument at its ROOT rule occurrence (position ε):
          -- the exception `record_from_crossing : forward_path_rewrite(C)` licenses
          -- defeating the inference, not the (genuinely observed) loss datum.
          DeclAttack (SUndercut (ArgId "d_comp") (ArgId "a_rec") [])
        , DeclStatus (PropId "c05_record")
        ]
    }

-- ===========================================================================
-- Example 3 — ls20 C08 vs C09: a refuted hypothesis, as a rebut
-- ===========================================================================

-- | ARC-AGI-3 ls20 claims __C08__ (refuted) vs __C09__ (supported). C08: "the L2
-- switch only flips top↔bottom, so a hidden second control is needed." C09: "one
-- switch (a 4-state cycle) alone suffices." A live solve made C08's conclusion
-- and C09's conclusion contrary; the C09 argument __rebuts__ the C08 argument at
-- its root conclusion.
--
-- ARA source (C08 refuted, C09 supported):
-- <https://github.com/ARA-Labs/ARA-Demo/blob/main/arc-agi3/ls20/logic/claims.md#L124-L157>
--
-- Presentation syntax:
--
-- > claim c08_hidden
-- >   nl     = "L2 needs a hidden second lock control"
-- >   formal = needs_second_control(ls20_L2)
-- > claim c09_single
-- >   nl     = "One 4-state-cycle switch solves L2 alone"
-- >   formal = single_switch_suffices(ls20_L2)
-- >
-- > leaf e_flip  : observed(single_stepon_looked_like_flip)  kind=observed
-- > leaf e_cycle : observed(repeated_stepons_cycle_middle_row)  kind=observed
-- >
-- > arg a08 : supports(c08_hidden) by undersampled_inference(e_flip)
-- > arg a09 : supports(c09_single) by repeated_sampling(e_cycle)
-- >
-- > rebut a09 a08         -- their conclusions are a declared contrary pair
-- >
-- > status c08_hidden     -- designed: defeated
-- > status c09_single     -- designed: justified
--
-- Designed statuses: __c08_hidden defeated__, __c09_single justified__. C08 rests
-- on an under-sampling artifact; the repeated-sampling argument for C09 rebuts it
-- on the declared contrary pair @{needs_second_control, single_switch_suffices}@,
-- exactly how the corpus records the hypothesis's disposition (C08 status:
-- refuted; C09 status: supported).
ls20SwitchDispute :: Program
ls20SwitchDispute =
  Program
    { programArtifact = "arc-agi3/ls20"
    , programDigest = Digest "sha256:ls20c09…"
    , programPolicy = PolicyId "puzzle-inference-v1"
    , programBackends = []
    , programDecls =
        [ DeclClaim
            Claim
              { claimId = PropId "c08_hidden"
              , claimNl = "L2 needs a hidden second lock control"
              , claimFormal = atom "needs_second_control" [con "ls20_L2"]
              , claimBinding =
                  Binding
                    { bindingAuthor = "codex"
                    , bindingRationale = "single observed step-on looked like a top-bottom flip"
                    , bindingAuditStatus = Disputed
                    }
              }
        , DeclClaim
            Claim
              { claimId = PropId "c09_single"
              , claimNl = "One 4-state-cycle switch solves L2 alone"
              , claimFormal = atom "single_switch_suffices" [con "ls20_L2"]
              , claimBinding =
                  Binding
                    { bindingAuthor = "codex"
                    , bindingRationale = "repeated sampling revealed a 4-state cycle reaching the target"
                    , bindingAuditStatus = Reviewed
                    }
              }
        , DeclLeaf $
            leaf
              "e_flip"
              (atom "observed" [con "single_stepon_looked_like_flip"])
              Observed
              AiExecuted
              ["trace/exploration_tree.yaml#N12"]
        , DeclLeaf $
            leaf
              "e_cycle"
              (atom "observed" [con "repeated_stepons_cycle_middle_row"])
              Observed
              AiExecuted
              ["logic/solution/heuristics.md#H06"]
        , DeclArg
            Arg
              { argId = ArgId "a08"
              , argConcl = SupportsClaim (PropId "c08_hidden")
              , argTerm =
                  inst
                    "undersampled_inference"
                    [(Param "Level", con "ls20_L2")]
                    [SLeaf (LeafId "e_flip")]
                    []
                    []
              }
        , DeclArg
            Arg
              { argId = ArgId "a09"
              , argConcl = SupportsClaim (PropId "c09_single")
              , argTerm =
                  inst
                    "repeated_sampling"
                    [(Param "Level", con "ls20_L2")]
                    [SLeaf (LeafId "e_cycle")]
                    []
                    []
              }
        , -- their conclusions are a policy-declared contrary pair; C09 rebuts C08
          DeclAttack (SRebut (ArgId "a09") (ArgId "a08"))
        , DeclStatus (PropId "c08_hidden")
        , DeclStatus (PropId "c09_single")
        ]
    }

-- ---------------------------------------------------------------------------
-- Index
-- ---------------------------------------------------------------------------

-- | All example programs paired with a label and the claim status each is
-- /designed/ to report once the checker exists.
allExamples :: [(String, Program, [(PropId, Status)])]
allExamples =
  [ ("nanogpt C02 tail-EMA (incomplete)", nanogptTailEma, [(PropId "c02", Gap)])
  ,
    ( "nanogpt C05 v12 quarantine (defeat)"
    , nanogptV12Quarantine
    , [(PropId "c05_record", Defeated)]
    )
  ,
    ( "ls20 C08 vs C09 switch dispute (rebut)"
    , ls20SwitchDispute
    , [(PropId "c08_hidden", Defeated), (PropId "c09_single", Justified)]
    )
  ]
