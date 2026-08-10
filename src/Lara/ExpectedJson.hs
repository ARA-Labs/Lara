-- | The @expected.json@ golden renderer for the worked-examples suite (M4a
-- Task A2).
--
-- == What this file is /for/
--
-- Each worked example already ships an @example.core.sexp@ wire anchor whose
-- verdict __class__ (accept + labels\/statuses, or @reject \<class\>@) both
-- drivers agree on byte-for-byte (the Haskell↔Lean differential). @expected.json@
-- adds the one thing the wire verdict deliberately drops: the __located
-- diagnostic__, which is __Haskell-only__ (the Lean driver emits only the wire
-- verdict, spec plan D16). So a golden here pins, per example:
--
--   * the __verdict class__ (@"accept"@ or @"reject \<class\>"@) — the same class
--     the differential compares across Haskell + Lean; and
--   * the __located diagnostic__ — for a reject, the offending
--     argument\/attack\/policy constituent and the failing stage
--     ("Lara.Diagnostics".'locate'); for an accept, the per-claim statuses plus
--     the gap\/incomplete-alternative reporting ("Lara.Reporting".'claimReports').
--
-- == Design
--
-- 'expectedJson' is a __pure__ function of a validated 'CheckInput': the exact
-- source replay identity plus the unchanged 'Unit' serialized into each
-- @.core.sexp@ anchor. IO (reading the @.lara@ + policy) lives in the
-- caller (@scripts\/gen-worked-examples.hs@ and @test\/WorkedExamplesSpec.hs@),
-- mirroring how the @.core.sexp@ generator is structured.
--
-- The JSON is emitted by a tiny hand-rolled pretty-printer ('renderJson') — the
-- codebase hand-rolls its codecs ("Lara.Wire"), and these files are small, so no
-- @aeson@ dependency is taken. String spellings for verdict classes reuse the
-- wire vocabulary ("Lara.Wire".'tagToString') so the JSON class atom is the exact
-- text the wire carries.
module Lara.ExpectedJson
  ( -- * The minimal JSON value + pretty-printer
    JValue (..)
  , renderJson
  , renderAttack
  , renderAttackKind
  , renderAttackTargetPath
    -- * The @expected.json@ golden for a checked unit
  , expectedJsonValue
  , expectedJson
  , sourceResultJsonValue
  ) where

import Data.Char (ord)
import Data.List (intercalate)
import Numeric (showHex)

import Lara.AST hiding (Claim, Reject)
import Lara.Check
  ( ProgramError (..)
  , UnitError (..)
  , checkUnit
  )
import Lara.Diagnostics
  ( Constituent (..)
  , LocatedRejection (..)
  , Stage (..)
  , locate
  )
import Lara.Driver
  ( buildCertOk
  , buildGamma
  , groupConflictMessage
  , groupConflictReject
  , groupConsistent
  , prune
  , pruneChecked
  , runCheck
  )
import Lara.Elaborate
  ( SourceResult
  , sourceResultCheckInput
  , sourceResultCheckedArgIds
  , sourceResultDiagnostics
  , sourceResultLocatedRejection
  , sourceResultVerdict
  )
import Lara.Grounded (Claim (..))
import Lara.Policy (lookupRule)
import Lara.Replay
  ( CheckInput
  , ReplayFailure (..)
  , ReplayId
  , inputReplayId
  , inputUnit
  , replayArtifact
  , replayBackends
  , replayCore
  , replayPolicy
  , replayTheories
  , runtimeReplayFailure
  )
import Lara.Prop (Prop, prettyProp)
import Lara.Reporting
  ( ClaimReport (..)
  , claimReports
  )
import Lara.SupportTerm
  ( CheckError (..)
  , CheckLoc (..)
  , ReferenceReason (..)
  )
import Lara.Wire
  ( Outcome (..)
  , PublicStatus (..)
  , Tag (..)
  , Verdict (..)
  , conditionalStatus
  , coreVersionText
  , isPublished
  , rejectClassTag
  , tagToString
  )

-- ---------------------------------------------------------------------------
-- The minimal JSON value + pretty-printer
-- ---------------------------------------------------------------------------

-- | A minimal JSON value. Only the arms the goldens need (no floating point:
-- every number here is a small non-negative index or count).
data JValue
  = JNull
  | JBool Bool
  | JNumber Int
  | JString String
  | JArray [JValue]
  | JObject [(String, JValue)]
  deriving (Eq, Show)

-- | Pretty-print a 'JValue' with 2-space indentation and a single trailing
-- newline. Object member order is preserved (goldens are byte-stable). Empty
-- arrays and objects render inline as @[]@ \/ @{}@.
renderJson :: JValue -> String
renderJson v = go 0 v ++ "\n"
  where
    go :: Int -> JValue -> String
    go _ JNull = "null"
    go _ (JBool b) = if b then "true" else "false"
    go _ (JNumber n) = show n
    go _ (JString s) = renderString s
    go _ (JArray []) = "[]"
    go i (JArray xs) =
      "[\n"
        ++ intercalate ",\n" [ind (i + 1) ++ go (i + 1) x | x <- xs]
        ++ "\n"
        ++ ind i
        ++ "]"
    go _ (JObject []) = "{}"
    go i (JObject kvs) =
      "{\n"
        ++ intercalate
          ",\n"
          [ind (i + 1) ++ renderString k ++ ": " ++ go (i + 1) x | (k, x) <- kvs]
        ++ "\n"
        ++ ind i
        ++ "}"
    ind n = replicate (n * 2) ' '

-- | Render a JSON string literal with the mandatory escapes (RFC 8259): the
-- quote, the backslash, the C0 control characters (as short escapes where one
-- exists, else @\\uXXXX@).
renderString :: String -> String
renderString s = '"' : concatMap esc s ++ "\""
  where
    esc c = case c of
      '"' -> "\\\""
      '\\' -> "\\\\"
      '\n' -> "\\n"
      '\r' -> "\\r"
      '\t' -> "\\t"
      '\b' -> "\\b"
      '\f' -> "\\f"
      _
        | ord c < 0x20 ->
            let h = showHex (ord c) ""
             in "\\u" ++ replicate (4 - length h) '0' ++ h
        | otherwise -> [c]

-- ---------------------------------------------------------------------------
-- The expected.json golden for a validated check input
-- ---------------------------------------------------------------------------

-- | The @expected.json@ content for a 'CheckInput': @renderJson@ of
-- 'expectedJsonValue', with the single trailing newline @renderJson@ appends.
-- This is the exact byte content the goldens store and the freshness test
-- reproduces.
expectedJson :: CheckInput -> String
expectedJson = renderJson . expectedJsonValue

-- | Render a source result without discarding its admission prune.  When the
-- audit is empty, the legacy raw-core rendering remains byte-identical.  A
-- policy-pruned result is rendered directly from its public verdict; rebuilding
-- it through 'runCheck' would lose the policy seed and blocked-status overlay.
sourceResultJsonValue :: SourceResult -> JValue
sourceResultJsonValue result =
  case sourceResultCheckInput result of
    Right input -> expectedJsonValue input
    Left _ ->
      case sourceResultVerdict result of
        Verdict replayId (Accept labels _edges statuses) ->
          JObject
            [ ("replay-id", replayIdValue replayId)
            , ("verdict-class", JString (tagToString TAccept))
            , ( "located-diagnostic"
              , JObject
                  [ ("kind", JString "accept")
                  , ("statuses", JArray (map sourceStatusEntry statuses))
                  , ("labels", JArray (map sourceLabelEntry labels))
                  ]
              )
            ]
        Verdict replayId (Reject rejection) ->
          JObject
            [ ("replay-id", replayIdValue replayId)
            , ("verdict-class", JString ("reject " ++ rejectionClass rejection))
            , ("located-diagnostic", sourceRejectDiagnostic result rejection)
            ]
  where
    sourceStatusEntry (p, status) =
      JObject $
        [ ("claim", JString (prettyProp p))
        , ("status", JString (publicStatusString status))
        ]
          ++ [ ("conditional-status", JString (statusString (conditionalStatus status)))
             | not (isPublished status)
             ]
    sourceLabelEntry (i, label) =
      JObject
        [ ("index", JNumber i)
        , ("label", JString (labelString label))
        ]

-- | The reject diagnostic of a policy-pruned source result.
--
-- The prune makes the declared 'CheckInput' unusable for re-deriving anything
-- ('sourceResultCheckInput' fails closed), so this renders straight from the
-- decision the source pipeline already made: the wire class, plus the failing
-- stage and offending constituent carried by 'sourceResultLocatedRejection' —
-- the /same/ decision path that produced the verdict. @messages@ retains the
-- driver's @stderr@ precedence lines, which exist only for the two boundary
-- rejections (R13, R9); every ordinary checker rejection reports itself through
-- @stage@ + @constituent@ instead, so rendering @messages@ alone would publish
-- an empty diagnostic for, say, a pruned R1.
sourceRejectDiagnostic :: SourceResult -> Rejection -> JValue
sourceRejectDiagnostic result rejection =
  JObject
    ( [ ("kind", JString "reject")
      , ("class", JString (rejectionClass rejection))
      ]
        ++ locatedFields
        ++ [("messages", JArray (map JString (sourceResultDiagnostics result)))]
    )
  where
    -- 'Nothing' only on acceptance, which this branch is not; the empty case is
    -- for totality.
    locatedFields = case sourceResultLocatedRejection result of
      Nothing -> []
      Just (LocatedRejection _ stage constituent) ->
        [ ("stage", JString (diagnosticStageString (CheckerStage stage)))
        , ("constituent", sourceConstituentValue (sourceResultCheckedArgIds result) constituent)
        ]

-- | Render a located constituent against the __checked__ argument ids (the
-- indices the checker used after the prune — see 'sourceResultCheckedArgIds').
-- Attacks are named by index only: the source boundary deliberately does not
-- export the checked unit, so there is no attack list to spell here.
sourceConstituentValue :: [ArgId] -> Constituent -> JValue
sourceConstituentValue argIds c = case c of
  CPolicy -> JObject [("kind", JString "policy")]
  CArgument i ->
    JObject ([("kind", JString "argument")] ++ argIdField i ++ [("index", JNumber i)])
  CAttack i -> JObject [("kind", JString "attack"), ("index", JNumber i)]
  CConflictPair i j ->
    JObject
      [ ("kind", JString "conflict-pair")
      , ("source", endpoint i)
      , ("target", endpoint j)
      ]
  CReplayEnvelope -> JObject [("kind", JString "replay")]
  CGroup (GroupId g) -> JObject [("kind", JString "group"), ("id", JString g)]
  where
    endpoint i = JObject (argIdField i ++ [("index", JNumber i)])
    argIdField i = [("id", JString a) | Just (ArgId a) <- [safeIndex argIds i]]

-- | The structured @expected.json@ value for a 'CheckInput' (pure).
--
-- The verdict is taken from the real pipeline ("Lara.Driver".'runCheck'), so
-- its identity, class, and accept statuses are exactly the wire verdict's.
-- On an ordinary reject, the located diagnostic is recovered from the
-- checker's 'UnitError' ("Lara.Check".'checkUnit' +
-- "Lara.Diagnostics".'locate') — the Haskell-only detail the wire drops.
expectedJsonValue :: CheckInput -> JValue
expectedJsonValue input =
  case runCheck input of
    Verdict _ (Accept labels _edges statuses) ->
      JObject
        [ ("replay-id", replayIdValue replayId)
        , ("verdict-class", JString (tagToString TAccept))
        , ("located-diagnostic", acceptDiag labels statuses)
        ]
    Verdict _ (Reject rejection) ->
      JObject
        [ ("replay-id", replayIdValue replayId)
        , ("verdict-class", JString ("reject " ++ rejectionClass rejection))
        , ("located-diagnostic", rejectDiagnostic)
        ]
  where
    replayId = inputReplayId input
    unit = inputUnit input
    -- Boundary rejections (R13 replay, R9 group conflict) never reach
    -- 'checkUnit', so 'rejectDiag' below cannot recover them — mirror 'runCheck's
    -- precedence and render them from the same source the drivers print.
    rejectDiagnostic =
      case runtimeReplayFailure input of
        Just failure -> replayFailureDiagnostic failure
        Nothing
          | groupConflictReject unit -> groupConflictDiagnostic unit
          | otherwise -> rejectDiag
    gamma = buildGamma (unitLeaves unit)
    certOk = buildCertOk (unitTheories unit)
    pI = lookupRule (unitRules unit)
    reports = claimReports pI gamma certOk unit

    -- Accept: per-claim statuses + Reporting detail, plus the per-argument
    -- grounded labels (both keyed to their declaration-order identity).
    acceptDiag :: [(Int, Label)] -> [(Prop, PublicStatus)] -> JValue
    acceptDiag lbls statuses =
      JObject
        [ ("kind", JString "accept")
        , ("statuses", JArray (zipWith statusEntry statuses reports))
        , ("labels", JArray (map labelEntry lbls))
        ]

    statusEntry :: (Prop, PublicStatus) -> ClaimReport -> JValue
    statusEntry (p, st) rep =
      JObject $
        [ ("claim", JString (prettyProp p))
        , ("status", JString (publicStatusString st))
        , ("complete-support", JNumber (length (claimSupport (crClaim rep))))
        , ("holes", JNumber (length (claimHoles (crClaim rep))))
        , ("incomplete-alternative", JBool (crIncompleteAlternative rep))
        ]
          -- Spec §4.3 / issue #76: an @evidence-blocked@ claim's four-state
          -- label is a conditional diagnostic, so it goes in its own field —
          -- mirroring the wire's statuses/conditional split — and never under
          -- @status@, which must agree with the verdict.
          ++ [ ("conditional-status", JString (statusString (conditionalStatus st)))
             | not (isPublished st)
             ]

    -- The verdict's labels cover the __checked__ (post-§4.3-quarantine)
    -- program, so the argument name must come from the checked argument list:
    -- indexing the declared list would misattribute every label after a pruned
    -- argument (issue #76 review round 2 — found while pinning the
    -- quarantine-attacker golden). With nothing quarantined the lists are equal.
    checkedArgs = unitArgs (pruneChecked (prune unit))

    labelEntry :: (Int, Label) -> JValue
    labelEntry (i, lbl) =
      JObject
        ( [("arg", JString a) | Just (ArgId a) <- [fmap fst (safeIndex checkedArgs i)]]
            ++ [ ("index", JNumber i)
               , ("label", JString (labelString lbl))
               ]
        )

    -- Reject: the located diagnostic recovered from the checker's UnitError —
    -- the wire class + stage + constituent, enriched with the offending
    -- leaf\/rule id and the term position where the checker's located error
    -- carries them (e.g. R1 names the missing leaf and its occurrence).
    rejectDiag :: JValue
    rejectDiag = case checkUnit gamma certOk unit of
      Right _ -> JNull -- unreachable: runCheck reported an ordinary rejection
      Left err ->
        let LocatedRejection rej stage constituent = locate err
         in JObject
              ( [ ("kind", JString "reject")
                , ("class", JString (rejectionClass rej))
                , ("stage", JString (diagnosticStageString (CheckerStage stage)))
                , ("constituent", constituentValue constituent)
                ]
                  ++ rejectDetail err
              )

    constituentValue :: Constituent -> JValue
    constituentValue c = case c of
      CPolicy -> JObject [("kind", JString "policy")]
      CArgument i ->
        JObject
          ( [("kind", JString "argument")]
              ++ argIdField i
              ++ [("index", JNumber i)]
          )
      CAttack i ->
        JObject
          ( [("kind", JString "attack"), ("index", JNumber i)]
              ++ [ ("attack", JString (renderAttack k))
                 | Just k <- [safeIndex (unitAttacks unit) i]
                 ]
          )
      CConflictPair i j ->
        JObject
          [ ("kind", JString "conflict-pair")
          , ("source", endpoint i)
          , ("target", endpoint j)
          ]
      -- The two boundary constituents are produced only by
      -- 'Lara.Driver.runCheckLocated'; 'locate' (this renderer's only source)
      -- never yields them, so these arms exist for totality alone and no golden
      -- exercises them.
      CReplayEnvelope -> JObject [("kind", JString "replay")]
      CGroup (GroupId g) -> JObject [("kind", JString "group"), ("id", JString g)]

    endpoint :: Int -> JValue
    endpoint i = JObject (argIdField i ++ [("index", JNumber i)])

    argIdField :: Int -> [(String, JValue)]
    argIdField i = [("id", JString a) | Just (ArgId a) <- [fmap fst (safeIndex (unitArgs unit) i)]]

replayIdValue :: ReplayId -> JValue
replayIdValue replayId =
  JObject
    [ ("core", JString (coreVersionText (replayCore replayId)))
    , ("policy", JString policy)
    , ("backends", JArray (map (JString . renderBackendRef) (replayBackends replayId)))
    , ("theories", JArray (map (JString . renderTheoryDigest) (replayTheories replayId)))
    , ("artifact", JString artifact)
    ]
  where
    PolicyId policy = replayPolicy replayId
    Digest artifact = replayArtifact replayId
    renderBackendRef (BackendId backend, version) = backend ++ "@" ++ version
    renderTheoryDigest (TheoryDigest theory) = theory

replayFailureDiagnostic :: ReplayFailure -> JValue
replayFailureDiagnostic failure =
  JObject
    [ ("kind", JString "reject")
    , ("class", JString (rejectionClass (RejectClass R13)))
    , ("stage", JString (diagnosticStageString ReplayPreflightStage))
    , ("constituent", constituent)
    , ("reason", JString reason)
    , ("backend", JString backendReference)
    ]
  where
    (constituent, reason, backendReference) = case failure of
      DuplicateSelectedBackend (BackendId backend) version ->
        ( JObject [("kind", JString "policy")]
        , "duplicate-selection"
        , backend ++ "@" ++ version
        )
      UnknownSelectedBackend (BackendId backend) version ->
        ( JObject [("kind", JString "policy")]
        , "unknown-selection"
        , backend ++ "@" ++ version
        )
      CertificateBackendNotSelected index (ArgId argumentId) (BackendId backend) version ->
        ( JObject
            [ ("kind", JString "argument")
            , ("id", JString argumentId)
            , ("index", JNumber index)
            ]
        , "certificate-backend-not-selected"
        , backend ++ "@" ++ show version
        )

-- | The R9 located diagnostic for an escalated duplicate-report-group conflict.
-- Like 'replayFailureDiagnostic', this is a boundary rejection that never reaches
-- 'checkUnit', so it is rendered directly: it names the first @≢@ group (in
-- declaration order) and its members, and carries the exact @stderr@ line
-- 'Lara.Driver.groupConflictMessage' prints.
groupConflictDiagnostic :: Unit -> JValue
groupConflictDiagnostic unit =
  JObject
    ( [ ("kind", JString "reject")
      , ("class", JString (rejectionClass (RejectClass R9)))
      , ("stage", JString (diagnosticStageString GroupBoundaryStage))
      ]
        ++ groupDetail
        ++ [("message", JString msg) | Just msg <- [groupConflictMessage unit]]
    )
  where
    groupDetail = case filter (not . groupConsistent unit) (unitGroups unit) of
      [] -> []
      DupGroup (GroupId g) members : _ ->
        [ ("constituent", JObject [("kind", JString "group"), ("id", JString g)])
        , ("members", JArray [JString m | LeafId m <- members])
        ]

-- ---------------------------------------------------------------------------
-- Renderers (closed vocabularies — one spelling table each)
-- ---------------------------------------------------------------------------

-- | The public claim status, exactly as the wire verdict spells it: the
-- four-state word, or @evidence-blocked@ when a §4.3 prune made the label
-- unpublishable (issue #76).
publicStatusString :: PublicStatus -> String
publicStatusString ps
  | isPublished ps = statusString (conditionalStatus ps)
  | otherwise = tagToString TEvidenceBlocked

-- | The four-state claim status, spelled as in @docs\/m4a-checklist.md@.
statusString :: Status -> String
statusString s = case s of
  Gap -> "gap"
  Justified -> "justified"
  Contested -> "contested"
  Defeated -> "defeated"

-- | The grounded argument label (in\/out\/undec).
labelString :: Label -> String
labelString l = case l of
  LIn -> "in"
  LOut -> "out"
  LUndec -> "undec"

-- | The stage a located diagnostic reports: one of the six 'checkUnit'
-- stages for an ordinary checker rejection ('CheckerStage'), or the replay
-- preflight for an R13 verdict ('ReplayPreflightStage', which has no
-- counterpart in the checker's closed 'Stage' sum).
data DiagnosticStage
  = CheckerStage Stage
  | ReplayPreflightStage
  | GroupBoundaryStage
  deriving (Eq, Show)

-- | The one spelling table for 'DiagnosticStage' (the goldens pin the
-- @backend@ preflight spelling and the @group-boundary@ R9 spelling).
diagnosticStageString :: DiagnosticStage -> String
diagnosticStageString ds = case ds of
  CheckerStage stage -> stageString stage
  ReplayPreflightStage -> "backend"
  GroupBoundaryStage -> "group-boundary"

-- | Which of the six 'checkUnit' stages produced a rejection.
stageString :: Stage -> String
stageString s = case s of
  StageDuplicateRule -> "duplicate-rule"
  StagePolicyWellFormedness -> "policy-well-formedness"
  StageDuplicateArgument -> "duplicate-argument"
  StageSupport -> "support"
  StageTypedAttack -> "typed-attack"
  StageMissingConflict -> "missing-conflict"
  -- Boundary stages: produced only by 'Lara.Driver.runCheckLocated', never by
  -- 'locate'. This renderer keeps the pre-existing 'DiagnosticStage' spellings
  -- for the goldens, so these arms are for totality only.
  StageReplayPreflight -> "backend"
  StageGroupBoundary -> "group-boundary"

-- | The wire class atom of a rejection (reusing the wire tag vocabulary so the
-- JSON text equals the @.core.sexp@ verdict's class atom).
rejectionClass :: Rejection -> String
rejectionClass r = tagToString $ case r of
  DuplicateRule -> TDupRule
  DuplicateArgument -> TDupArgument
  IncompleteArgument -> TIncompleteArgument
  MissingConflict -> TMissingConflict
  -- Reuse the wire tag table as the single source of truth so every
  -- 'RejectClass' (incl. R9) is covered and the two can never drift.
  RejectClass c -> rejectClassTag c

-- | Extra located detail recovered from a whole-unit rejection: for a wrapped
-- located checker failure ('PERejection'), the offending leaf\/rule id and the
-- term position ("Lara.SupportTerm".'CheckLoc') the checker recorded. Structural
-- program-boundary outcomes (duplicate rule\/argument, incomplete argument,
-- missing conflict) and policy violations carry no such inner detail, so they add
-- nothing here (their constituent already locates them).
rejectDetail :: UnitError -> [(String, JValue)]
rejectDetail e = case e of
  UEProgram (PERejection _ ce) -> checkErrorDetail ce
  _ -> []

-- | The offending id + term position of a located checker error. R1 reference
-- failures name the missing leaf or rule; the other classes contribute their
-- term position where one is recorded (best-effort — the constituent already
-- carries the primary location).
checkErrorDetail :: CheckError -> [(String, JValue)]
checkErrorDetail ce = case ce of
  CE_R1 loc (MissingLeaf (LeafId l)) ->
    [("reason", JString "missing-leaf"), ("leaf", JString l), termPos loc]
  CE_R1 loc (MissingRule (RuleId r)) ->
    [("reason", JString "missing-rule"), ("rule", JString r), termPos loc]
  CE_R1 loc (UndeclaredAttackSource _) ->
    [("reason", JString "undeclared-attack-source"), termPos loc]
  CE_R1 loc (UndeclaredAttackTarget _) ->
    [("reason", JString "undeclared-attack-target"), termPos loc]
  _ -> []
  where
    termPos loc = ("term-position", JString (renderCheckLoc loc))

-- | Render a support-term occurrence ("Lara.SupportTerm".'CheckLoc') as a path
-- from the root: @root@, @root.premise i@, @root.q q@ (nested).
renderCheckLoc :: CheckLoc -> String
renderCheckLoc LocRoot = "root"
renderCheckLoc (LocPremise l i) = renderCheckLoc l ++ ".premise " ++ show i
renderCheckLoc (LocQuestion l (QuestionId q)) = renderCheckLoc l ++ ".q " ++ q

-- | Render a typed attack in the surface style @kind src tgt[\@position]@ (names
-- the offending attack + its position for the located reject diagnostic).
renderAttack :: Attack -> String
renderAttack attack =
  renderAttackKind attack ++ case attack of
    Rebut (ArgId w) (ArgId u) -> " " ++ w ++ " " ++ u
    Undercut (ArgId w) (ArgId u) position ->
      " " ++ w ++ " " ++ u ++ renderPosition position
    Undermine (ArgId w) (ArgId u) position ->
      " " ++ w ++ " " ++ u ++ renderPosition position

renderAttackKind :: Attack -> String
renderAttackKind Rebut {} = "rebut"
renderAttackKind Undercut {} = "undercut"
renderAttackKind Undermine {} = "undermine"

renderAttackTargetPath :: Attack -> String
renderAttackTargetPath Rebut {} = "root"
renderAttackTargetPath (Undercut _ _ position) = renderPositionId position "rule"
renderAttackTargetPath (Undermine _ _ position) = renderPositionId position "leaf"

renderPositionId :: Position -> String -> String
renderPositionId position terminal =
  intercalate "." (map renderStep position ++ [terminal])

-- | Render an attack position path @\@i.q.…@ (empty at the root).
renderPosition :: Position -> String
renderPosition [] = ""
renderPosition steps = "@" ++ intercalate "." (map renderStep steps)

renderStep :: Step -> String
renderStep (StepPremise i) = show i
renderStep (StepQuestion (QuestionId q)) = q

-- | Total list indexing.
safeIndex :: [a] -> Int -> Maybe a
safeIndex xs i
  | i < 0 = Nothing
  | otherwise = case drop i xs of
      (x : _) -> Just x
      [] -> Nothing
