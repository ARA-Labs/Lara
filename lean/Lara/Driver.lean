/-
The Lean executable semantics driver (M3 plan, Task 0 Step 3 — the N11
differential anchor's Lean side).

This is a THIN decode → call → encode shim. It contains no checker or grounding
logic of its own: it parses one wire S-expression (the format frozen by the
Haskell codec `src/Lara/Wire.hs`), decodes it into the symbolic core, calls the
theorem-bearing definitions of the Lean development (`Lara.Check.Unit.checkUnit`,
`Lara.Grounded.grounded`/`labelC`/`statusC`, `Lara.Compile.checkedAF`/`edgeB`,
`Lara.Consistency.completeClaimFor`), and re-encodes the verdict.

Contract (identical to `app/Main.hs`, plan D16):
* `lara-driver <file.sexp>` reads one wire check-input envelope, runs replay
  preflight before the checker, and prints an identity-bearing S-expression
  verdict on `stdout`, byte-identical to `Lara.Wire.encodeVerdict`.
* Exit codes: `0` = accept, `1` = checker rejection, `2` = codec / usage error
  (with a located message on `stderr`).

Symbolic-core discipline (repo `CLAUDE.md`): raw `String`s appear only at the
textual boundary (`Sx`, the pre-parse token tree, and the closed `Tag` table
that mirrors `Lara.Wire.tagToString`). Everything inward is the closed symbolic
core of the Lean development.

Design decisions (documented, faithful to the mechanized development):
* `canon := Lara.canonNum`. Numeric literals therefore use the same identity
  relation as the Haskell production driver; identifier canonicalization remains
  the separate `canonId = id` extension point.
* The backend registry is built from the wire `theories` section over the three
  implemented backend cores — `nd@1` (`Lara.Strict.ndBackend`, digests resolving
  to ND-encoded theory data), `ra@1` and `ord@1` (`Lara.RA.raBackend` /
  `Lara.Ord.ordBackend`, known digests resolving to the **empty** theory because
  both are premise-only). See `buildRegistry` for why the two resolutions
  differ. Units that reference any other backend fall through to a certificate
  rejection, which is the honest behaviour given only these three are
  mechanized.
* The verdict is printed followed by a single `\n`, matching the Haskell
  CLI's `putStrLn`: both drivers' stdout is `printSExpr (encodeVerdict v)`
  plus one newline, so differential comparison is byte equality.
-/

import Lara.Consistency
import Lara.Blocked
import Lara.BlockedProgram
import Lara.RawAttack
import Lara.Groups
import Lara.Strict
import Lara.RA
import Lara.Ord

namespace Lara.Driver

open Lara Lara.Support Lara.Attack Lara.RawAttack Lara.Policy
open Lara.Check Lara.Check.Unit
open Lara.Grounded Lara.Compile Lara.Consistency

/-- The production driver's numeric-literal canonicalizer (see `Lara.Prop`). -/
def dcanon : String → String := Lara.canonNum

/-! ### The textual S-expression token tree (the one place raw `String` lives) -/

/-- Pre-parse S-expression: an untyped atom string or a list, like a JSON
lexer's value. Distinct from `Lara.Support.SExpr` (the abstract certificate
payload) by design. -/
inductive Sx where
  | atom : String → Sx
  | list : List Sx → Sx
deriving Inhabited

private instance : Inhabited SExpr := ⟨.atom ""⟩

/-! ### The closed wire keyword vocabulary (mirrors `Lara.Wire.Tag`) -/

/-- Every keyword of the wire grammar, as a closed sum type. Concrete spellings
live in exactly one place, `tagToString`, textually mirroring the Haskell
`Lara.Wire.tagToString` table. -/
inductive Tag where
  | unit | policy | rules | rule | mode | params | premises | conclusion
  | questions | question | allowTrusted | certifiers | certifier | contraries
  | contrary | exceptions | exception | theories | theory | leaves | leaf
  | args | arg | attacks | queries | subst | discharges | holes | assurance
  | cert | pos | prem | ques | inst
  | strict | defeasible | mandatory | optional | truE | falsE | nonE | trusted
  | var | numLit | strLit | conApp | atom | apat
  | rebut | undercut | undermine
  | checkInput | replayId | core | backends | backend | artifact
  | verdict | accept | reject | labels | edges | statuses | status | conditional
  | inL | outL | undecL | gap | justified | contested | defeated | evidenceBlocked
  | dupRule | dupArgument | incompleteArgument | missingConflict
  | groups | group | quarantine
  -- the many-sorted signature Sigma (spec §2, §3.4; lara-core@0.2)
  | sigma | sorts | cons | preds | «pred»
  | r1 | r2 | r3 | r4 | r5 | r6 | r7 | r9 | r10 | r11 | r12 | r13

/-- The on-the-wire spelling of a keyword — the single source of truth. -/
def tagToString : Tag → String
  | .unit => "unit" | .policy => "policy" | .rules => "rules" | .rule => "rule"
  | .mode => "mode" | .params => "params" | .premises => "premises"
  | .conclusion => "conclusion" | .questions => "questions"
  | .question => "question" | .allowTrusted => "allow-trusted"
  | .certifiers => "certifiers" | .certifier => "certifier"
  | .contraries => "contraries" | .contrary => "contrary"
  | .exceptions => "exceptions" | .exception => "exception"
  | .theories => "theories" | .theory => "theory" | .leaves => "leaves"
  | .leaf => "leaf" | .args => "args" | .arg => "arg" | .attacks => "attacks"
  | .queries => "queries" | .subst => "subst" | .discharges => "discharges"
  | .holes => "holes" | .assurance => "assurance" | .cert => "cert"
  | .pos => "pos" | .prem => "prem" | .ques => "ques" | .inst => "inst"
  | .strict => "strict" | .defeasible => "defeasible"
  | .mandatory => "mandatory" | .optional => "optional"
  | .truE => "true" | .falsE => "false" | .nonE => "none" | .trusted => "trusted"
  | .var => "var" | .numLit => "num" | .strLit => "str" | .conApp => "con"
  | .atom => "atom" | .apat => "apat"
  | .rebut => "rebut" | .undercut => "undercut" | .undermine => "undermine"
  | .checkInput => "check-input" | .replayId => "replay-id" | .core => "core"
  | .backends => "backends" | .backend => "backend" | .artifact => "artifact"
  | .verdict => "verdict" | .accept => "accept" | .reject => "reject"
  | .labels => "labels" | .edges => "edges" | .statuses => "statuses"
  | .conditional => "conditional"
  | .status => "status"
  | .inL => "in" | .outL => "out" | .undecL => "undec"
  | .gap => "gap" | .justified => "justified" | .contested => "contested"
  | .defeated => "defeated" | .evidenceBlocked => "evidence-blocked"
  | .dupRule => "duplicate-rule" | .dupArgument => "duplicate-argument"
  | .incompleteArgument => "incomplete-argument"
  | .missingConflict => "missing-conflict"
  | .groups => "groups" | .group => "group" | .quarantine => "quarantine"
  | .sigma => "sigma" | .sorts => "sorts" | .cons => "cons"
  | .preds => "preds" | .pred => "pred"
  | .r1 => "R1" | .r2 => "R2" | .r3 => "R3" | .r4 => "R4" | .r5 => "R5" | .r6 => "R6"
  | .r7 => "R7" | .r9 => "R9" | .r10 => "R10" | .r11 => "R11" | .r12 => "R12"
  | .r13 => "R13"

/-! ### Canonical printer (byte-identical to `Lara.Wire.printSExpr`) -/

/-- Bare-atom character set: printable ASCII except `(`, `)`, `;`, `"`, `\`. -/
def isBareChar (c : Char) : Bool :=
  let o := c.toNat
  Nat.ble 0x21 o && Nat.ble o 0x7e &&
    !(c == '(' || c == ')' || c == ';' || c == '"' || c == '\\')

def escChar (c : Char) : String :=
  if c == '"' then "\\\""
  else if c == '\\' then "\\\\"
  else if c == '\n' then "\\n"
  else String.singleton c

def printAtom (s : String) : String :=
  if s != "" && s.all isBareChar then s
  else "\"" ++ String.join (s.toList.map escChar) ++ "\""

partial def printSx : Sx → String
  | .atom s => printAtom s
  | .list xs => "(" ++ String.intercalate " " (xs.map printSx) ++ ")"

/-! ### The textual reader (mirrors `Lara.Wire.parseSExpr`) -/

structure PState where
  input : List Char
  line : Nat
  col : Nat

def PState.err (p : PState) (msg : String) : Except String α :=
  .error ("line " ++ toString p.line ++ ", column " ++ toString p.col ++ ": " ++ msg)

def step (p : PState) : PState :=
  match p.input with
  | '\n' :: rest => { input := rest, line := p.line + 1, col := 1 }
  | _ :: rest => { p with input := rest, col := p.col + 1 }
  | [] => p

partial def skipComment (p : PState) : PState :=
  match p.input with
  | '\n' :: _ => p
  | [] => p
  | _ => skipComment (step p)

partial def skipSpace (p : PState) : PState :=
  match p.input with
  | c :: _ =>
    if c == ' ' || c == '\t' || c == '\n' || c == '\r' then skipSpace (step p)
    else if c == ';' then skipSpace (skipComment (step p))
    else p
  | [] => p

def spanBare : List Char → (List Char × List Char)
  | [] => ([], [])
  | c :: rest =>
    if isBareChar c then
      let (a, b) := spanBare rest
      (c :: a, b)
    else ([], c :: rest)

mutual
  partial def parseForm (p : PState) : Except String (Sx × PState) :=
    match p.input with
    | '(' :: _ => parseList (step p) []
    | '"' :: _ => parseQuoted (step p) []
    | c :: _ =>
      if isBareChar c then
        let (tok, rest) := spanBare p.input
        let p' := { p with input := rest, col := p.col + tok.length }
        .ok (.atom (String.ofList tok), p')
      else p.err ("unexpected character '" ++ String.singleton c ++ "'")
    | [] => p.err "unexpected end of input"

  partial def parseList (p : PState) (acc : List Sx) : Except String (Sx × PState) :=
    let p' := skipSpace p
    match p'.input with
    | ')' :: _ => .ok (.list acc.reverse, step p')
    | [] => p'.err "unclosed list"
    | _ => do
        let (e, p'') ← parseForm p'
        parseList p'' (e :: acc)

  partial def parseQuoted (p : PState) (acc : List Char) : Except String (Sx × PState) :=
    match p.input with
    | '"' :: _ => .ok (.atom (String.ofList acc.reverse), step p)
    | '\\' :: [] => p.err "unterminated escape sequence"
    | '\\' :: c :: _ =>
        if c == '"' then parseQuoted (step (step p)) ('"' :: acc)
        else if c == '\\' then parseQuoted (step (step p)) ('\\' :: acc)
        else if c == 'n' then parseQuoted (step (step p)) ('\n' :: acc)
        else p.err ("invalid escape sequence \\" ++ String.singleton c)
    | [] => p.err "unterminated string literal"
    | c :: _ => parseQuoted (step p) (c :: acc)
end

/-- Parse exactly one top-level form; a second form is an error. -/
def parseWire (input : String) : Except String Sx := do
  let start := skipSpace { input := input.toList, line := 1, col := 1 }
  let (e, rest) ← parseForm start
  let rest' := skipSpace rest
  if rest'.input.isEmpty then .ok e
  else rest'.err "expected a single S-expression, found more input"

/-! ### Decode helpers -/

def sxAtom (ctx : String) : Sx → Except String String
  | .atom s => .ok s
  | _ => .error (ctx ++ ": expected an atom")

/-- Match `(tag fields*)` and return the fields. -/
def sectionFields (ctx : String) (t : Tag) (e : Sx) : Except String (List Sx) :=
  match e with
  | .list (.atom k :: fs) =>
    if k == tagToString t then .ok fs
    else .error (ctx ++ ": expected (" ++ tagToString t ++ " …)")
  | _ => .error (ctx ++ ": expected (" ++ tagToString t ++ " …)")

/-- Match a tagged list with exactly `arity` payload fields. -/
def matchTagged (ctx : String) (t : Tag) (arity : Nat) (e : Sx) :
    Except String (List Sx) :=
  match e with
  | .list (.atom k :: fs) =>
    if k == tagToString t then
      if fs.length == arity then .ok fs
      else .error (ctx ++ ": wrong number of fields for " ++ tagToString t)
    else .error (ctx ++ ": expected (" ++ tagToString t ++ " …)")
  | _ => .error (ctx ++ ": expected (" ++ tagToString t ++ " …)")

/-- Canonical decimal natural: no sign, no leading zeros. Bounded to the
Haskell driver's 64-bit `Int` range (`Lara.Wire.parseNatText` rejects larger
values via its canonical-reprint check), so the two codecs accept exactly the
same NAT texts. -/
def parseNat (ctx : String) (s : String) : Except String Nat :=
  match s.toNat? with
  | some n => if toString n == s && n ≤ 0x7fffffffffffffff then .ok n
              else .error (ctx ++ ": malformed natural number: " ++ s)
  | none => .error (ctx ++ ": malformed natural number: " ++ s)

def decodeBool (ctx : String) : Sx → Except String Bool
  | .atom s =>
    if s == tagToString .truE then .ok true
    else if s == tagToString .falsE then .ok false
    else .error (ctx ++ ": expected true|false")
  | _ => .error (ctx ++ ": expected true|false")

def termsOfList : List Term → Terms
  | [] => .nil
  | t :: ts => .cons t (termsOfList ts)

def patsOfList : List Pat → Pats
  | [] => .nil
  | p :: ps => .cons p (patsOfList ps)

def termsToList : Terms → List Term
  | .nil => []
  | .cons t ts => t :: termsToList ts

/-! ### Terms, patterns, atoms -/

partial def decodeTerm (e : Sx) : Except String Term :=
  match e with
  | .list (.atom k :: fields) =>
    if k == tagToString .numLit then
      match fields with | [.atom s] => .ok (.num s) | _ => .error "term: malformed num"
    else if k == tagToString .strLit then
      match fields with | [.atom s] => .ok (.str s) | _ => .error "term: malformed str"
    else if k == tagToString .conApp then
      match fields with
      | (.atom h) :: ts => (ts.mapM decodeTerm).map (fun ts' => .con h (termsOfList ts'))
      | _ => .error "term: malformed con"
    else .error ("term: unknown tag " ++ k)
  | _ => .error "term: expected list"

partial def decodePat (e : Sx) : Except String Pat :=
  match e with
  | .list (.atom k :: fields) =>
    if k == tagToString .var then
      match fields with | [.atom x] => .ok (.var ⟨x⟩) | _ => .error "pattern: malformed var"
    else if k == tagToString .numLit then
      match fields with | [.atom s] => .ok (.num s) | _ => .error "pattern: malformed num"
    else if k == tagToString .strLit then
      match fields with | [.atom s] => .ok (.str s) | _ => .error "pattern: malformed str"
    else if k == tagToString .conApp then
      match fields with
      | (.atom h) :: ps => (ps.mapM decodePat).map (fun ps' => .con ⟨h⟩ (patsOfList ps'))
      | _ => .error "pattern: malformed con"
    else .error ("pattern: unknown tag " ++ k)
  | _ => .error "pattern: malformed pattern"

def decodeAtom (e : Sx) : Except String Atom :=
  match e with
  | .list (.atom k :: fields) =>
    if k == tagToString .atom then
      match fields with
      | (.atom p) :: ts => (ts.mapM decodeTerm).map (fun ts' => .atom p (termsOfList ts'))
      | _ => .error "atom: malformed atom"
    else .error ("atom: expected (atom …), got tag " ++ k)
  | _ => .error "atom: expected (atom …)"

def decodeAPat (e : Sx) : Except String APat :=
  match e with
  | .list (.atom k :: fields) =>
    if k == tagToString .apat then
      match fields with
      | (.atom p) :: ps => (ps.mapM decodePat).map (fun ps' => ⟨⟨p⟩, patsOfList ps'⟩)
      | _ => .error "atom pattern: malformed atom pattern"
    else .error ("atom pattern: expected (apat …), got tag " ++ k)
  | _ => .error "atom pattern: malformed atom pattern"

/-! ### Substitutions, assurance, support terms -/

def decodeSubst (e : Sx) : Except String Subst := do
  let fs ← sectionFields "substitution" .subst e
  fs.mapM (fun b =>
    match b with
    | .list [x, tm] => do
        let xs ← sxAtom "substitution" x
        let t ← decodeTerm tm
        .ok ((⟨xs⟩ : VarId), t)
    | _ => .error "substitution: malformed binding")

partial def toCertSExpr : Sx → SExpr
  | .atom s => .atom s
  | .list xs => .list (xs.map toCertSExpr)

def decodeAssuranceVal (e : Sx) : Except String Assurance :=
  match e with
  | .atom s =>
    if s == tagToString .nonE then .ok .none
    else if s == tagToString .trusted then .ok .trusted
    else .error "assurance: malformed assurance"
  | .list (.atom k :: fields) =>
    if k == tagToString .cert then
      match fields with
      | [b, v, h, payload] => do
          let name ← sxAtom "assurance" b
          let vs ← sxAtom "assurance" v
          let ver ← parseNat "assurance" vs
          let hs ← sxAtom "assurance" h
          .ok (.cert ⟨name, ver⟩ ⟨hs⟩ ⟨toCertSExpr payload⟩)
      | _ => .error "assurance: malformed cert"
    else .error "assurance: malformed assurance"
  | _ => .error "assurance: malformed assurance"

mutual
  partial def decodeSupportTerm (e : Sx) : Except String SupportTerm :=
    match e with
    | .list (.atom k :: fields) =>
      if k == tagToString .leaf then
        match fields with | [.atom l] => .ok (.leaf ⟨l⟩) | _ => .error "support term: malformed leaf"
      else if k == tagToString .inst then
        match fields with
        | [rS, substS, premsS, dischS, holesS, assuranceS] => do
            let rs ← sxAtom "support term" rS
            let theta ← decodeSubst substS
            let prems ← (sectionFields "premises" .premises premsS) >>= (·.mapM decodeSupportTerm)
            let disch ← (sectionFields "discharges" .discharges dischS) >>= (·.mapM decodeDischarge)
            let holes ← (sectionFields "holes" .holes holesS) >>=
              (·.mapM (fun h => (sxAtom "holes" h).map (fun s => (⟨s⟩ : QuestionId))))
            let av ← matchTagged "assurance" .assurance 1 assuranceS
            let assurance ← (match av with | [a'] => decodeAssuranceVal a' | _ => .error "assurance: arity")
            .ok (.inst ⟨rs⟩ theta prems disch holes assurance)
        | _ => .error "support term: malformed inst"
      else .error ("support term: unknown tag " ++ k)
    | _ => .error "support term: malformed support term"

  partial def decodeDischarge (e : Sx) : Except String (QuestionId × SupportTerm) :=
    match e with
    | .list [q, w] => do
        let qs ← sxAtom "discharges" q
        let w' ← decodeSupportTerm w
        .ok ((⟨qs⟩ : QuestionId), w')
    | _ => .error "discharges: malformed discharge"
end

/-! ### Positions and attacks (endpoints resolved after decode) -/

def decodePosition (e : Sx) : Except String Pos := do
  let fs ← sectionFields "position" .pos e
  fs.mapM (fun s =>
    match s with
    | .list (.atom k :: rest) =>
      if k == tagToString .prem then
        match rest with
        | [.atom i] => (parseNat "position" i).map (fun n => (PosElem.prem n))
        | _ => .error "position: malformed prem"
      else if k == tagToString .ques then
        match rest with
        | [.atom q] => .ok (PosElem.ques ⟨q⟩)
        | _ => .error "position: malformed ques"
      else .error ("position: unknown step " ++ k)
    | _ => .error "position: malformed position step")

/-! ### Attacks (endpoints resolved after decode) -/

def decodeAttack (e : Sx) : Except String RawAttack :=
  match e with
  | .list (.atom k :: fields) =>
    if k == tagToString .rebut then
      match fields with
      | [.atom w, .atom u] => .ok (.rebut w u)
      | _ => .error "attack: malformed rebut"
    else if k == tagToString .undercut then
      match fields with
      | [.atom w, .atom u, posS] => (decodePosition posS).map (fun π => .undercut w u π)
      | _ => .error "attack: malformed undercut"
    else if k == tagToString .undermine then
      match fields with
      | [.atom w, .atom u, posS] => (decodePosition posS).map (fun π => .undermine w u π)
      | _ => .error "attack: malformed undermine"
    else .error ("attack: unknown kind " ++ k)
  | _ => .error "attack: malformed attack"

/-! ### Rules, contraries, exceptions, policy -/

def decodeQuestion (e : Sx) : Except String Question := do
  let fs ← matchTagged "question" .question 3 e
  match fs with
  | [qid, ap, nec] => do
      let q ← sxAtom "question" qid
      let a ← decodeAPat ap
      let m ← (match nec with
        | .atom s =>
          if s == tagToString .mandatory then .ok true
          else if s == tagToString .optional then .ok false
          else .error "question: expected mandatory|optional"
        | _ => .error "question: expected mandatory|optional")
      .ok ⟨⟨q⟩, a, m⟩
  | _ => .error "question: arity"

def decodeCertifier (e : Sx) : Except String (BackendId × Digest) := do
  let fs ← matchTagged "certifier" .certifier 3 e
  match fs with
  | [b, v, h] => do
      let name ← sxAtom "certifier" b
      let vs ← sxAtom "certifier" v
      let ver ← parseNat "certifier" vs
      let hs ← sxAtom "certifier" h
      .ok ((⟨name, ver⟩ : BackendId), (⟨hs⟩ : Digest))
  | _ => .error "certifier: arity"

def decodeRule (e : Sx) : Except String RuleDecl := do
  let fs ← matchTagged "rule" .rule 8 e
  match fs with
  | [rid, modeS, paramsS, premsS, conclS, qsS, atS, certsS] => do
      let ridS ← sxAtom "rule" rid
      let mode ← (do
        let m ← matchTagged "rule mode" .mode 1 modeS
        match m with
        | [.atom s] =>
          if s == tagToString .strict then .ok Mode.strict
          else if s == tagToString .defeasible then .ok Mode.defeasible
          else .error "rule mode: expected strict|defeasible"
        | _ => .error "rule mode")
      let params ← (sectionFields "rule params" .params paramsS) >>=
        (·.mapM (fun x => (sxAtom "rule params" x).map (fun s => (⟨s⟩ : VarId))))
      let prems ← (sectionFields "rule premises" .premises premsS) >>= (·.mapM decodeAPat)
      let concl ← (do
        let c ← matchTagged "rule conclusion" .conclusion 1 conclS
        match c with | [c'] => decodeAPat c' | _ => .error "rule conclusion")
      let qs ← (sectionFields "rule questions" .questions qsS) >>= (·.mapM decodeQuestion)
      let allowT ← (do
        let b ← matchTagged "rule allow-trusted" .allowTrusted 1 atS
        match b with | [b'] => decodeBool "rule allow-trusted" b' | _ => .error "rule allow-trusted")
      let certs ← (sectionFields "rule certifiers" .certifiers certsS) >>= (·.mapM decodeCertifier)
      .ok ⟨⟨ridS⟩,
        { mode := mode, params := params, premises := prems, concl := concl
        , questions := qs, allowTrusted := allowT, certifiers := certs }⟩
  | _ => .error "rule: arity"

def decodeContrary (e : Sx) : Except String (APat × APat) := do
  let fs ← matchTagged "contrary" .contrary 2 e
  match fs with
  | [a, b] => do
      let a' ← decodeAPat a
      let b' ← decodeAPat b
      .ok (a', b')
  | _ => .error "contrary: arity"

def decodeException (e : Sx) : Except String (RuleId × APat) := do
  let fs ← matchTagged "exception" .exception 2 e
  match fs with
  | [r, ap] => do
      let rs ← sxAtom "exception" r
      let ap' ← decodeAPat ap
      .ok ((⟨rs⟩ : RuleId), ap')
  | _ => .error "exception: arity"

/-! ### The signature section (`lara-core@0.2`)

A sort *reference* is an atom: the two reserved base names, or a declared sort
name. A sort *declaration* is a bare name, so `(sort Num)` is representable and
rejected by the checker as base-sort shadowing rather than being unspellable. -/

def decodeSort (e : Sx) : Except String Lara.Sigma.TermSort :=
  match e with
  | .atom "Num" => .ok .num
  | .atom "Str" => .ok .str
  | .atom n => .ok (.decl n)
  | _ => .error "sigma sort: expected an atom"

def decodeConSig (e : Sx) : Except String Lara.Sigma.ConSig :=
  match e with
  | .list [.atom k, .atom nm, argsE, resE] =>
      if k == tagToString .conApp then do
        let args ← (sectionFields "sigma con args" .args argsE) >>= (·.mapM decodeSort)
        let res ← decodeSort resE
        .ok ⟨⟨nm⟩, args, res⟩
      else .error "sigma con: expected con tag"
  | _ => .error "sigma con: malformed constructor signature"

def decodePredSig (e : Sx) : Except String Lara.Sigma.PredSig :=
  match e with
  | .list [.atom k, .atom nm, argsE] =>
      if k == tagToString .pred then do
        let args ← (sectionFields "sigma pred args" .args argsE) >>= (·.mapM decodeSort)
        .ok ⟨⟨nm⟩, args⟩
      else .error "sigma pred: expected pred tag"
  | _ => .error "sigma pred: malformed predicate signature"

/-- Decode the optional `sigma` section. An absent section is the empty
signature, which under strict mode accepts only symbol-free units. -/
def decodeSigmaSection : Option Sx → Except String Lara.Sigma.Sigma
  | none => .ok Lara.Sigma.Sigma.empty
  | some s => do
      match ← sectionFields "sigma" .sigma s with
      | [sortsE, consE, predsE] => do
          let sorts ← (sectionFields "sigma sorts" .sorts sortsE) >>= (·.mapM
            (fun x => match x with
                      | .atom n => .ok n
                      | _ => .error "sigma sorts: expected an atom"))
          let cons ← (sectionFields "sigma cons" .cons consE) >>= (·.mapM decodeConSig)
          let preds ← (sectionFields "sigma preds" .preds predsE) >>= (·.mapM decodePredSig)
          .ok ⟨sorts, cons, preds⟩
      | _ => .error "sigma: arity"

def decodePolicy :
    Option Sx →
    Except String (List RuleDecl × List (APat × APat) × List (RuleId × APat))
  | none => .ok ([], [], [])
  | some s => do
      let fs ← matchTagged "policy" .policy 3 s
      match fs with
      | [rulesS, contrariesS, exceptionsS] => do
          let rules ← (sectionFields "policy rules" .rules rulesS) >>= (·.mapM decodeRule)
          let contraries ← (sectionFields "policy contraries" .contraries contrariesS)
            >>= (·.mapM decodeContrary)
          let exceptions ← (sectionFields "policy exceptions" .exceptions exceptionsS)
            >>= (·.mapM decodeException)
          .ok (rules, contraries, exceptions)
      | _ => .error "policy: arity"

/-! ### The remaining sections -/

def decodeTheories : Option Sx → Except String (List (Digest × List Atom))
  | none => .ok []
  | some s => do
      let fs ← sectionFields "theories" .theories s
      fs.mapM (fun t => do
        let tf ← sectionFields "theory" .theory t
        match tf with
        | h :: atoms => do
            let hs ← sxAtom "theory" h
            let props ← atoms.mapM decodeAtom
            .ok ((⟨hs⟩ : Digest), props)
        | [] => .error "theory: malformed theory")

def decodeLeaves : Option Sx → Except String (List (LeafId × Atom))
  | none => .ok []
  | some s => do
      let fs ← sectionFields "leaves" .leaves s
      fs.mapM (fun l => do
        let lf ← matchTagged "leaf" .leaf 2 l
        match lf with
        | [lid, a] => do
            let ls ← sxAtom "leaf" lid
            let p ← decodeAtom a
            .ok ((⟨ls⟩ : LeafId), p)
        | _ => .error "leaf: arity")

def decodeArgs : Option Sx → Except String (List (String × SupportTerm))
  | none => .ok []
  | some s => do
      let fs ← sectionFields "args" .args s
      fs.mapM (fun a => do
        let af ← matchTagged "arg" .arg 2 a
        match af with
        | [aid, st] => do
            let as ← sxAtom "arg" aid
            let t ← decodeSupportTerm st
            .ok (as, t)
        | _ => .error "arg: arity")

def decodeAttacks : Option Sx → Except String (List RawAttack)
  | none => .ok []
  | some s => (sectionFields "attacks" .attacks s) >>= (·.mapM decodeAttack)

def decodeQueries : Option Sx → Except String (List Atom)
  | none => .ok []
  | some s => (sectionFields "queries" .queries s) >>= (·.mapM decodeAtom)

/-! ### Duplicate-report groups (spec §4.3) -/

def decodeGroupMembers : Sx → Except String (List LeafId)
  | .list ms => ms.mapM (fun m =>
      match m with
      | .atom l => .ok (⟨l⟩ : LeafId)
      | _ => .error "group member: expected atom")
  | _ => .error "group members: expected list"

def decodeGroup (e : Sx) : Except String Groups.DupGroup :=
  match e with
  | .list [.atom k, .atom gid, membersS] =>
      if k != tagToString .group then .error "group: expected group tag"
      else do
        let members ← decodeGroupMembers membersS
        .ok { id := gid, members := members }
  | _ => .error "group: malformed group"

/-- Decode the optional `groups` section: the conflict mode, then one group per
declared duplicate-report group. Mirrors `Lara.Wire.decodeGroups`. -/
def decodeGroups :
    Option Sx → Except String (List Groups.DupGroup × Groups.GroupConflictMode)
  | none => .ok ([], .quarantine)
  | some s => do
      let fs ← sectionFields "groups" .groups s
      match fs with
      | modeE :: groupEs => do
          let mode ← (match modeE with
            | .atom m =>
                if m == tagToString .quarantine then
                  (.ok .quarantine : Except String Groups.GroupConflictMode)
                else if m == tagToString .reject then
                  .ok .reject
                else .error "groups mode: unknown group conflict mode"
            | _ => .error "groups mode: malformed group mode")
          let groups ← groupEs.mapM decodeGroup
          .ok (groups, mode)
      | [] => .error "groups: groups section missing its conflict mode"

/-! ### Wire well-formedness invariants (R14) and endpoint resolution -/

def firstDup : List String → List String → Option String
  | [], _ => none
  | x :: rest, seen => if seen.contains x then some x else firstDup rest (x :: seen)

/-- A `none` scan saw no element that was already accumulated. -/
private theorem firstDup_none_not_seen :
    ∀ (xs seen : List String), firstDup xs seen = none → ∀ x ∈ xs, x ∉ seen := by
  intro xs
  induction xs with
  | nil => intro _ _ x hx; simp at hx
  | cons head tail ih =>
      intro seen h x hx
      by_cases hhead : head ∈ seen
      · simp [firstDup, hhead] at h
      · have htail : firstDup tail (head :: seen) = none := by
          simpa [firstDup, hhead] using h
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hhead
        · have hnot := ih (head :: seen) htail x hx
          exact fun hin => hnot (by simp [hin])

/-- **`firstDup` decides R14 uniqueness.**  A `none` scan is a `Nodup` proof, so
the wire decoder's duplicate-id rejection can hand its callers the invariant
itself rather than a discarded boolean.  Consumers that resolve by id (raw
attack endpoints, quarantine retention) need that proof: with duplicate ids a
kept id no longer implies the kept row is the one the id resolves to. -/
theorem firstDup_none_nodup :
    ∀ (xs seen : List String), firstDup xs seen = none → xs.Nodup := by
  intro xs
  induction xs with
  | nil => intro _ _; exact List.nodup_nil
  | cons head tail ih =>
      intro seen h
      by_cases hhead : head ∈ seen
      · simp [firstDup, hhead] at h
      · have htail : firstDup tail (head :: seen) = none := by
          simpa [firstDup, hhead] using h
        refine List.nodup_cons.mpr ⟨?_, ih (head :: seen) htail⟩
        intro hmem
        exact (firstDup_none_not_seen tail (head :: seen) htail head hmem) (by simp)

/-! ### Building the checker inputs -/

def buildGamma (leaves : List (LeafId × Atom)) : LeafId → Option Atom :=
  fun l => (leaves.find? (fun e => decide (e.1 = l))).map (·.2)

/-- The reference backend identity, `nd@1`. -/
def ndBackendId : BackendId := ⟨"nd", 1⟩

/-- The rational-arithmetic backend identity, `ra@1`. -/
def raBackendId : BackendId := ⟨"ra", 1⟩

/-- The ordered-comparison backend identity, `ord@1`. -/
def ordBackendId : BackendId := ⟨"ord", 1⟩

/-- Backend registry built from the wire `theories` section over the fixed
`nd@1` / `ra@1` / `ord@1` triple, mirroring the Haskell `buildCertOk`: each
fixed core, with each declared digest resolving to that digest's core-encoded
theory data.

The two rational-arithmetic backends are the exception, and deliberately so: a
*known* `ra@1` or `ord@1` digest resolves to the **empty** theory rather than
to the declared entries (an unknown digest still fails to resolve, which is a
rejection).  Both are premise-only by design (`Lara.Ord` §2.2; the seam-wide
decision extending it to `ra@1`), and this is what keeps the two sides in exact
agreement: each Haskell adapter rejects any certificate slot at or beyond the
premise count, while the abstract `Backend` core is handed only `Γ = Δ ++ T`
and never learns `Δ.length`.  Resolving to `[]` makes `Γ = Δ`, so "names a
premise" and "is in range of `Γ`" coincide and both sides accept exactly the
same certificates — including on a unit that declares a non-empty wire theory,
where the Haskell side rejects those slots outright.

Only `nd@1` still resolves a digest to its declared entries, because its
consulted context genuinely is `Δ ++ T`: an `nd@1` certificate's de Bruijn free
variables are meant to reach theory axioms. -/
def buildRegistry (theories : List (Digest × List Atom)) : BackendRegistry dcanon :=
  fun β =>
    if β = ndBackendId then
      some { core := Lara.Strict.ndBackend dcanon
             resolveTheory := fun h =>
               match theories.find? (fun t => decide (t.1 = h)) with
               | some t => some (t.2.map (Lara.Strict.ndEnc dcanon))
               | none => none }
    else if β = raBackendId then
      some { core := Lara.RA.raBackend dcanon
             resolveTheory := fun h =>
               match theories.find? (fun t => decide (t.1 = h)) with
               | some _ => some []
               | none => none }
    else if β = ordBackendId then
      some { core := Lara.Ord.ordBackend dcanon
             resolveTheory := fun h =>
               match theories.find? (fun t => decide (t.1 = h)) with
               | some _ => some []
               | none => none }
    else none

/-- The decoded wire unit plus the derived checker inputs. Only `Type 0` data
is stored here — the backend registry (which lives in `Type 1`, since a
`Backend` carries a `Form : Type` field) is built from `theories` outside the
decode monad. -/
structure Decoded where
  sigma : Lara.Sigma.Sigma
  policy : Policy
  args : List SupportTerm
  argIds : List String
  atts : List Attack
  gamma : LeafId → Option Atom
  theories : List (Digest × List Atom)
  queries : List Atom
  -- Raw pieces retained for the §4.3 duplicate-report-group boundary check,
  -- which runs after replay preflight (on the full args) and before the
  -- checker (on the quarantine-filtered args).
  leaves : List (LeafId × Atom)
  argsRaw : List (String × SupportTerm)
  -- R14 argument-id uniqueness, carried as a proof rather than re-decided:
  -- every consumer that resolves an endpoint or a retention decision by id
  -- depends on it (`Lara.RawAttack.lookupArg_of_mem_nodup`).
  argIdsNodup : (argsRaw.map (·.1)).Nodup
  attacksRaw : List RawAttack
  attacksAligned : resolveAttacks argsRaw attacksRaw = .ok atts
  groups : List Groups.DupGroup
  groupMode : Groups.GroupConflictMode

/-! ### Validated replay boundary -/

/-- The one supported core-version spelling — the single source of truth,
mirroring `Lara.Wire.coreVersionText`. -/
def coreVersionText : String := "lara-core@0.2"

structure ReplayId where
  core : String
  policy : String
  backends : List (String × String)
  theories : List String
  artifact : String

structure CheckInput where
  replayId : ReplayId
  decoded : Decoded

def compareCharLists : List Char → List Char → Ordering
  | [], [] => .eq
  | [], _ => .lt
  | _, [] => .gt
  | a :: as, b :: bs =>
      if a.toNat < b.toNat then .lt
      else if b.toNat < a.toNat then .gt
      else compareCharLists as bs

def compareCodePointString (a b : String) : Ordering :=
  compareCharLists a.toList b.toList

def insertCodePointString (s : String) : List String → List String
  | [] => [s]
  | x :: xs =>
      if compareCodePointString s x == .lt then s :: x :: xs
      else x :: insertCodePointString s xs

def sortCodePointStrings (xs : List String) : List String :=
  xs.foldr insertCodePointString []

def strictlySortedStrings : List String → Bool
  | [] | [_] => true
  | a :: b :: rest =>
      compareCodePointString a b == .lt &&
        strictlySortedStrings (b :: rest)

/-- Peel one optional, ordered section. -/
def takeSection (t : Tag) (ss : List Sx) : Option Sx × List Sx :=
  match ss with
  | s :: rest =>
    match s with
    | .list (.atom k :: _) => if k == tagToString t then (some s, rest) else (none, ss)
    | _ => (none, ss)
  | [] => (none, ss)

/-- Wire well-formedness (R14) for groups, mirroring `Lara.Wire`: unique group
ids, ≥2 distinct members, all declared leaves. -/
def checkGroupInvariants (groups : List Groups.DupGroup)
    (leaves : List (LeafId × Atom)) : Except String _root_.Unit := do
  let _ ← (match firstDup (groups.map (·.id)) [] with
           | some g => (.error ("groups: duplicate group id: " ++ g) : Except String _root_.Unit)
           | none => .ok ())
  let declared := leaves.map (fun e => e.1.name)
  groups.forM (fun g => do
    let names := g.members.map (·.name)
    let _ ← (match firstDup names [] with
             | some l => (.error ("group " ++ g.id ++ " repeats member: " ++ l) : Except String _root_.Unit)
             | none => .ok ())
    let _ ← (if names.length < 2 then
               (.error ("group " ++ g.id ++ " has fewer than two members") : Except String _root_.Unit)
             else .ok ())
    names.forM (fun l =>
      if declared.contains l then (.ok () : Except String _root_.Unit)
      else .error ("group " ++ g.id ++ " member is not a declared leaf: " ++ l)))

def decodeUnit (e : Sx) : Except String Decoded := do
  let sections ← sectionFields "unit" .unit e
  let sSigma := takeSection .sigma sections
  let s0 := takeSection .policy sSigma.2
  let s1 := takeSection .theories s0.2
  let s2 := takeSection .leaves s1.2
  let s3 := takeSection .args s2.2
  let s4 := takeSection .attacks s3.2
  let s5 := takeSection .queries s4.2
  let s6 := takeSection .groups s5.2
  let _ ← (if s6.2.isEmpty then (.ok () : Except String _root_.Unit)
           else .error "unit: unexpected section")
  let sigma ← decodeSigmaSection sSigma.1
  let pol ← decodePolicy s0.1
  let theories ← decodeTheories s1.1
  let leaves ← decodeLeaves s2.1
  let argsRaw ← decodeArgs s3.1
  let attacksRaw ← decodeAttacks s4.1
  let queries ← decodeQueries s5.1
  let (groups, groupMode) ← decodeGroups s6.1
  -- Retain the scan's equation: R14 uniqueness leaves this decoder as a proof
  -- on `Decoded`, not as a discarded boolean.
  match hDup : firstDup (argsRaw.map (·.1)) [] with
  | some dup => .error ("args: duplicate argument id: " ++ dup)
  | none => do
    let _ ← checkGroupInvariants groups leaves
    match hAtts : resolveAttacks argsRaw attacksRaw with
    | .error msg => .error msg
    | .ok atts =>
      .ok
        { sigma := sigma
        , policy := { rules := pol.1, defeat := ⟨pol.2.1, pol.2.2⟩ }
        , args := argsRaw.map (·.2)
        , argIds := argsRaw.map (·.1)
        , atts := atts
        , gamma := buildGamma leaves
        , theories := theories
        , queries := queries
        , leaves := leaves
        , argsRaw := argsRaw
        , argIdsNodup := firstDup_none_nodup _ _ hDup
        , attacksRaw := attacksRaw
        , attacksAligned := hAtts
        , groups := groups
        , groupMode := groupMode }

def decodeReplayBackend (e : Sx) : Except String (String × String) :=
  match e with
  | .list [.atom k, .atom name, .atom version] =>
      if k == tagToString .backend then .ok (name, version)
      else .error "replay backend: expected backend tag"
  | _ => .error "replay backend: malformed backend"

def validateReplayId (core : String) (policy : String)
    (backends : List (String × String)) (theories : List String)
    (artifact : String) : Except String ReplayId :=
  if strictlySortedStrings theories then
    .ok
      { core := core
      , policy := policy
      , backends := backends
      , theories := theories
      , artifact := artifact }
  else .error "replay-id: theories must be strictly sorted"

def validateTheoryIdentity (rid : ReplayId) (decoded : Decoded) :
    Except String _root_.Unit :=
  let keys := decoded.theories.map (fun entry =>
    match entry.1 with | ⟨s⟩ => s)
  match firstDup keys [] with
  | some digest => .error ("unit theories: duplicate digest: " ++ digest)
  | none =>
      if sortCodePointStrings keys == rid.theories then .ok ()
      else .error "check-input: replay theories differ from unit theories"

/-- Decode and validate the replay identity. The check order mirrors Haskell's
`decodeReplayIdM`: replay-id tag (and arity, via the outer match) first, then
the core section tag, then the core version value, then — in wire order — each
remaining section's tag check immediately followed by its payload decode
(policy, backends, theories, artifact), and finally the canonical-order
validation. -/
def decodeReplayId (e : Sx) : Except String ReplayId :=
  match e with
  | .list [.atom replayTag,
      .list [.atom coreTag, .atom core],
      .list [.atom policyTag, .atom policy],
      .list (.atom backendsTag :: backends),
      .list (.atom theoriesTag :: theories),
      .list [.atom artifactTag, .atom artifact]] => do
      let _ ←
        if replayTag != tagToString .replayId then
          (.error "replay-id: wrong field order" : Except String _root_.Unit)
        else .ok ()
      let _ ←
        if coreTag != tagToString .core then
          (.error "replay-id: wrong field order" : Except String _root_.Unit)
        else .ok ()
      let _ ←
        if core != coreVersionText then
          (.error "replay-id: unsupported core version" : Except String _root_.Unit)
        else .ok ()
      let _ ←
        if policyTag != tagToString .policy then
          (.error "replay-id: wrong field order" : Except String _root_.Unit)
        else .ok ()
      let _ ←
        if backendsTag != tagToString .backends then
          (.error "replay-id: wrong field order" : Except String _root_.Unit)
        else .ok ()
      let refs ← backends.mapM decodeReplayBackend
      let _ ←
        if theoriesTag != tagToString .theories then
          (.error "replay-id: wrong field order" : Except String _root_.Unit)
        else .ok ()
      let digests ← theories.mapM (sxAtom "replay theory")
      let _ ←
        if artifactTag != tagToString .artifact then
          (.error "replay-id: wrong field order" : Except String _root_.Unit)
        else .ok ()
      validateReplayId core policy refs digests artifact
  | _ => .error "replay-id: malformed replay identity"

def decodeCheckInput (e : Sx) : Except String CheckInput :=
  match e with
  | .list [.atom k, ridS, unitS] =>
      if k != tagToString .checkInput then
        .error "check-input: expected check-input tag"
      else do
        let rid ← decodeReplayId ridS
        let decoded ← decodeUnit unitS
        validateTheoryIdentity rid decoded
        .ok
          { replayId := rid
          , decoded := decoded }

  | _ => .error "check-input: malformed check input"

def backendPair (backend : BackendId) : String × String :=
  (backend.name, toString backend.version)

def firstDuplicateBackend : List (String × String) →
    List (String × String) → Option (String × String)
  | [], _ => none
  | backend :: rest, seen =>
      if seen.contains backend then some backend
      else firstDuplicateBackend rest (backend :: seen)

/-- The supported backend selections, mirroring `Lara.Replay.supportedBackends`. -/
def supportedBackends : List (String × String) :=
  [backendPair ndBackendId, backendPair raBackendId, backendPair ordBackendId]

def firstUnknownBackend : List (String × String) → Option (String × String)
  | [] => none
  | backend :: rest =>
      if !supportedBackends.contains backend then some backend
      else firstUnknownBackend rest

def firstSome {α β : Type} (f : α → Option β) : List α → Option β
  | [] => none
  | x :: xs =>
      match f x with
      | some value => some value
      | none => firstSome f xs

partial def firstUnselectedCertificate
    (selected : List (String × String)) : SupportTerm → Option BackendId
  | .leaf _ => none
  | .inst _ _ premises discharges _ assurance =>
      let atNode :=
        match assurance with
        | .cert backend _ _ =>
            if selected.contains (backendPair backend) then none else some backend
        | _ => none
      match atNode with
      | some backend => some backend
      | none =>
          match firstSome (firstUnselectedCertificate selected) premises with
          | some backend => some backend
          | none =>
              firstSome
                (fun discharge => firstUnselectedCertificate selected discharge.2)
                discharges

inductive ReplayFailure where
  | duplicateSelectedBackend : (String × String) → ReplayFailure
  | unknownSelectedBackend : (String × String) → ReplayFailure
  | unselectedCertificate : Nat → String → BackendId → ReplayFailure

/-- Visit the arguments in wire order (mirroring `Lara.Replay.firstUnselectedCertificate`):
the first argument, with its 0-based index and wire id, whose support tree carries a
certificate from an unselected backend. -/
def firstUnselectedCertInArgs (selected : List (String × String)) :
    List (String × SupportTerm) → Nat → Option ReplayFailure
  | [], _ => none
  | (argId, term) :: rest, index =>
      match firstUnselectedCertificate selected term with
      | some backend => some (.unselectedCertificate index argId backend)
      | none => firstUnselectedCertInArgs selected rest (index + 1)

def runtimeReplayFailure (rid : ReplayId) (argIds : List String)
    (args : List SupportTerm) : Option ReplayFailure :=
  match firstDuplicateBackend rid.backends [] with
  | some backend => some (.duplicateSelectedBackend backend)
  | none =>
      match firstUnknownBackend rid.backends with
      | some backend => some (.unknownSelectedBackend backend)
      | none => firstUnselectedCertInArgs rid.backends (argIds.zip args) 0

/-- The stderr diagnostic for a replay preflight failure — mirrors the Haskell
CLI's `replayFailureMessage` templates. -/
def replayFailureMessage : ReplayFailure → String
  | .duplicateSelectedBackend (name, version) =>
      "replay preflight: duplicate selected backend " ++ name ++ "@" ++ version
  | .unknownSelectedBackend (name, version) =>
      "replay preflight: unknown selected backend " ++ name ++ "@" ++ version
  | .unselectedCertificate index argId backend =>
      "replay preflight: certificate backend not selected: argument " ++ argId
        ++ " (index " ++ toString index ++ ") uses " ++ backend.name
        ++ "@" ++ toString backend.version

/-- The stderr diagnostic for an escalated group-conflict rejection (R9): the
first `≢` group in declaration order and its members. Mirrors the Haskell
`Lara.Driver.groupConflictMessage` byte-for-byte so both drivers' stderr is
comparable (the R13 `replayFailureMessage` precedent). `none` when no group is
inconsistent — the caller only prints it on the R9 branch. -/
def groupConflictMessage (canon : String → String)
    (leaves : List (LeafId × Atom)) (groups : List Groups.DupGroup) : Option String :=
  match groups.find? (fun g => ! Groups.consistentB canon leaves g) with
  | none => none
  | some g =>
      some ("group '" ++ g.id ++ "': members "
        ++ String.intercalate ", " (g.members.map (·.name))
        ++ " report one cell with ≢ propositions and "
        ++ "the policy escalates conflicts to reject (§4.3)")

/-! ### Verdict encoders (mirror `Lara.Wire.encodeVerdict`) -/

def sxNat (n : Nat) : Sx := .atom (toString n)

partial def encodeTerm : Term → Sx
  | .num s => .list [.atom (tagToString .numLit), .atom s]
  | .str s => .list [.atom (tagToString .strLit), .atom s]
  | .con k ts => .list (.atom (tagToString .conApp) :: .atom k :: (termsToList ts).map encodeTerm)

def encodeAtom : Atom → Sx
  | .atom p ts => .list (.atom (tagToString .atom) :: .atom p :: (termsToList ts).map encodeTerm)

def labelStr : Label → String
  | .inn => tagToString .inL
  | .out => tagToString .outL
  | .undec => tagToString .undecL

def statusStr : Status → String
  | .gap => tagToString .gap
  | .justified => tagToString .justified
  | .contested => tagToString .contested
  | .defeated => tagToString .defeated

def checkClassStr : RejectClass → String
  | .R1 => tagToString .r1 | .R2 => tagToString .r2
  | .R3 => tagToString .r3 | .R4 => tagToString .r4
  | .R5 => tagToString .r5 | .R6 => tagToString .r6 | .R7 => tagToString .r7
  | .R9 => tagToString .r9
  | .R10 => tagToString .r10 | .R11 => tagToString .r11
  | .R12 => tagToString .r12 | .R13 => tagToString .r13

/-- The closed wire `REJECTION` vocabulary, mirroring `Lara.Wire`'s rejection
spellings: either a checker rejection class or one of the four unit-level
failure keywords. Concrete spellings live in exactly one place,
`wireRejectionString`. -/
inductive WireRejection where
  | rejectClass : RejectClass → WireRejection
  | duplicateRule
  | duplicateArgument
  | incompleteArgument
  | missingConflict

/-- The on-the-wire spelling of a rejection — the single source of truth. -/
def wireRejectionString : WireRejection → String
  | .rejectClass cls => checkClassStr cls
  | .duplicateRule => tagToString .dupRule
  | .duplicateArgument => tagToString .dupArgument
  | .incompleteArgument => tagToString .incompleteArgument
  | .missingConflict => tagToString .missingConflict

/-- The wire rejection for a `checkUnit` failure — the wire `REJECTION`
vocabulary of `Lara.Wire`. -/
def rejectWire : UnitError → WireRejection
  | .duplicateRule _ => .duplicateRule
  | .signature _ => .rejectClass .R2
  | .scopeViolation _ => .rejectClass .R12
  | .policyViolation _ => .rejectClass .R12
  | .program e =>
    match e with
    | .rejection _ ce => .rejectClass ce.rejectClass
    | .duplicateArgument _ _ => .duplicateArgument
    | .incompleteArgument _ _ => .incompleteArgument
    | .missingConflict _ => .missingConflict

def encodeReplayId (rid : ReplayId) : Sx :=
  .list
    [ .atom (tagToString .replayId)
    , .list [.atom (tagToString .core), .atom rid.core]
    , .list [.atom (tagToString .policy), .atom rid.policy]
    , .list (.atom (tagToString .backends) ::
        rid.backends.map (fun bv =>
          .list [.atom (tagToString .backend), .atom bv.1, .atom bv.2]))
    , .list (.atom (tagToString .theories) :: rid.theories.map .atom)
    , .list [.atom (tagToString .artifact), .atom rid.artifact]
    ]

def encodeReject (rid : ReplayId) (cls : WireRejection) : Sx :=
  .list [.atom (tagToString .verdict), encodeReplayId rid,
    .atom (tagToString .reject), .atom (wireRejectionString cls)]

/-- The public status of one query (issue #76) — mirrors
`Lara.Wire.PublicStatus`. `published` is an ordinary four-state answer;
`evidenceBlocked` says §4.3 quarantine edited the program under the claim, so
its four-state label is only a conditional diagnostic. Keeping the conditional
label *inside* the constructor (instead of a parallel `blocked : List Atom`)
makes an orphan, permuted, or duplicated blocked query unrepresentable: both
verdict sections below are projections of one list. -/
inductive PublicStatus where
  | published (st : Status)
  | evidenceBlocked (conditional : Status)
  deriving Repr, DecidableEq

/-- The accept verdict. An `evidenceBlocked` status prints `evidence-blocked`
in the `statuses` section and its conditional label moves to a trailing
`conditional` section, which is emitted only when something is blocked. With
nothing blocked this is the pre-#76 encoding byte-for-byte. Mirrors
`Lara.Wire.encodeVerdict`. -/
def encodeAccept (rid : ReplayId) (labels : List (Nat × Label))
    (edges : List (Nat × Nat)) (statuses : List (Atom × PublicStatus)) : Sx :=
  let conditional := statuses.filterMap (fun ps =>
    match ps.2 with
    | .published _ => none
    | .evidenceBlocked st => some (ps.1, st))
  .list
    ([ .atom (tagToString .verdict)
     , encodeReplayId rid
     , .atom (tagToString .accept)
     , .list (.atom (tagToString .labels) ::
         labels.map (fun le => .list [sxNat le.1, .atom (labelStr le.2)]))
     , .list (.atom (tagToString .edges) ::
         edges.map (fun ij => .list [sxNat ij.1, sxNat ij.2]))
     , .list (.atom (tagToString .statuses) ::
         statuses.map (fun ps =>
           .list [.atom (tagToString .status), encodeAtom ps.1,
             .atom (match ps.2 with
                    | .published st => statusStr st
                    | .evidenceBlocked _ => tagToString .evidenceBlocked)]))
     ] ++
     (if conditional.isEmpty then [] else
       [ .list (.atom (tagToString .conditional) ::
           conditional.map (fun ps =>
             .list [.atom (tagToString .status), encodeAtom ps.1,
               .atom (statusStr ps.2)])) ]))

/-! ### Conservative reporting for quarantine-affected queries (spec §4.3, #76)

The seed and declared-index framework definitions live in
`Lara.BlockedProgram`, where the three abstract `Blocking` obligations are
*proved* (`blocking_of_blockedSeed`). That module also transports the compact AF
and `completeClaimFor` support labelled below through the retained-index
embedding and instantiates production non-promotion (issue #80). The Haskell
counterpart is `src/Lara/Blocked.hs`. -/

/-- The queries whose public status is `evidence-blocked`: those with a complete
support argument in the forward closure of the seed. A query with no complete
support is `gap` and is never blocked — losing support cannot promote a claim. -/
def blockedQueries (keep : (String × SupportTerm) → Bool)
    (declared : List (String × SupportTerm))
    (declAtts keptAtts : List Attack) (support : Atom → List Nat)
    (queries : List Atom) : List Atom :=
  BlockedProgram.blockedQueries keep declared declAtts keptAtts support queries

/-- Read the accept verdict off an accepted unit: grounded labels over the
compiled AF (`checkedAF`), the compiled closure edges in ascending order, and
one public status per query atom in query order — `evidenceBlocked` for the
queries in `blocked`, carrying the four-state label as its conditional
diagnostic. -/
def buildAccept {Γ : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    (rid : ReplayId) (accepted : Lara.Unit.CheckedUnit dcanon Γ CertOk)
    (queries : List Atom) (blocked : List Atom) : Sx :=
  let P := accepted.program
  let af := checkedAF P
  let n := P.args.length
  let labels := (List.range n).map (fun i => (i, labelC af i))
  let edges := (List.range n).foldr
    (fun i acc => (List.range n).foldr
      (fun j acc2 => if af.attack i j then (i, j) :: acc2 else acc2) acc) []
  let statuses := queries.map (fun p =>
    let st := statusC af (completeClaimFor accepted p)
    (p, if blocked.contains p then PublicStatus.evidenceBlocked st
        else PublicStatus.published st))
  encodeAccept rid labels edges statuses

/-! ### The driver -/

def runOnContents (contents : String) : IO _root_.Unit := do
  match parseWire contents with
  | .error msg =>
      IO.eprintln ("lara-driver: codec error at " ++ msg)
      IO.Process.exit 2
  | .ok e =>
    match decodeCheckInput e with
    | .error msg =>
        IO.eprintln ("lara-driver: codec error at " ++ msg)
        IO.Process.exit 2
    | .ok input =>
      let rid := input.replayId
      let d := input.decoded
      match runtimeReplayFailure rid d.argIds d.args with
      | some failure =>
          IO.eprintln (replayFailureMessage failure)
          IO.println (printSx (encodeReject rid (.rejectClass .R13)))
          IO.Process.exit 1
      | none =>
          -- §4.3 duplicate-report-group boundary: an escalated conflict rejects
          -- (R9); otherwise every argument using a quarantined leaf is dropped
          -- so its claim surfaces as gap (quarantine is not a rejection).
          if Groups.conflictReject dcanon d.groupMode d.leaves d.groups then
            match groupConflictMessage dcanon d.leaves d.groups with
            | some msg => IO.eprintln msg
            | none => pure ()
            IO.println (printSx (encodeReject rid (.rejectClass .R9)))
            IO.Process.exit 1
          else
            let qs := Groups.quarantined dcanon d.leaves d.groups
            let keep := Groups.keepArg qs
            let keptArgsRaw := BlockedProgram.retainedArguments keep d.argsRaw
            let keptIds := keptArgsRaw.map (·.1)
            let keepAttack := fun ra =>
              let (s, t) := ra.endpoints
              keptIds.contains s && keptIds.contains t
            let atts := selectAligned keepAttack d.attacksRaw d.atts
            let reg := buildRegistry d.theories
            let gamma := buildGamma (Groups.quarantineLeaves qs d.leaves)
            -- The finite ground atoms stage 2 sorts: Γ's surviving leaf
            -- conclusions, the backend theory table, and the queried claim
            -- atoms. They are passed explicitly because `Unit` carries Γ as a
            -- function; the Haskell mirror reads the same three lists off its
            -- own `Unit`, in the same stage.
            let ground :=
              (Groups.quarantineLeaves qs d.leaves).map (·.2)
                ++ d.theories.flatMap (·.2)
                ++ d.queries
            match checkUnit gamma reg ground
                ({ sigma := d.sigma
                 , policy := d.policy
                 , args := keptArgsRaw.map (·.2), atts := atts } : Lara.Unit) with
            | .error err =>
                IO.println (printSx (encodeReject rid (rejectWire err)))
                IO.Process.exit 1
            | .ok accepted =>
                -- The checker and the blocking proof consume the same
                -- filtered sublist of the already-resolved declared attacks.
                -- Thus the accepted program's compact AF is connected to the
                -- declared-index framework by construction, rather than by an
                -- unproved re-resolution equivalence.
                let blocked :=
                  blockedQueries keep d.argsRaw d.atts atts
                    (fun p => claimSupportFor accepted p) d.queries
                IO.println (printSx (buildAccept rid accepted d.queries blocked))

/-- Executable entry point: `lara-driver <file.sexp>`. -/
def main (args : List String) : IO _root_.Unit := do
  match args with
  | [path] => do
      let contents ← (do
        try
          IO.FS.readFile (⟨path⟩ : System.FilePath)
        catch _ =>
          IO.eprintln ("lara-driver: cannot read " ++ path)
          IO.Process.exit 2)
      runOnContents contents
  | _ =>
      IO.eprintln "usage: lara-driver <file.sexp>"
      IO.Process.exit 2

end Lara.Driver
