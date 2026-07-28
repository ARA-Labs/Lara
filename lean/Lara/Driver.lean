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
* `lara-driver <file.sexp>` reads one wire unit and prints an S-expression
  verdict on `stdout`, byte-identical to `Lara.Wire.encodeVerdict`.
* Exit codes: `0` = accept, `1` = checker rejection, `2` = codec / usage error
  (with a located message on `stderr`).

Symbolic-core discipline (repo `CLAUDE.md`): raw `String`s appear only at the
textual boundary (`Sx`, the pre-parse token tree, and the closed `Tag` table
that mirrors `Lara.Wire.tagToString`). Everything inward is the closed symbolic
core of the Lean development.

Design decisions (documented, faithful to the mechanized development):
* `canon := id`. The Lean development's example theorems check units at the
  identity canonicalizer (`Lara.Prop` fixes `canonId = id`; numeric literal
  normalization is the deferred extension point). The two fixtures do not
  involve numeric literals, so this reproduces the goldens exactly.
* The backend registry is built from the wire `theories` section over the one
  implemented backend, `nd@1` (`Lara.Strict.ndBackendWithTheory`), mirroring
  `Lara.Examples.registryEx`. Units that reference other backends fall through
  to a certificate rejection, which is the honest behaviour given only ND is
  mechanized.
* The verdict is printed followed by a single `\n`, matching the Haskell
  CLI's `putStrLn`: both drivers' stdout is `printSExpr (encodeVerdict v)`
  plus one newline, so differential comparison is byte equality.
-/

import Lara.Consistency
import Lara.Strict

namespace Lara.Driver

open Lara Lara.Support Lara.Attack Lara.Policy Lara.Check Lara.Check.Unit
open Lara.Grounded Lara.Compile Lara.Consistency

/-- The driver's canonicalizer (identity; see the file header). -/
def dcanon : String → String := fun s => s

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
  | verdict | accept | reject | labels | edges | statuses | status
  | inL | outL | undecL | gap | justified | contested | defeated
  | dupRule | dupArgument | incompleteArgument | missingConflict
  | r1 | r3 | r4 | r5 | r6 | r7 | r10 | r11 | r12 | r13

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
  | .verdict => "verdict" | .accept => "accept" | .reject => "reject"
  | .labels => "labels" | .edges => "edges" | .statuses => "statuses"
  | .status => "status"
  | .inL => "in" | .outL => "out" | .undecL => "undec"
  | .gap => "gap" | .justified => "justified" | .contested => "contested"
  | .defeated => "defeated"
  | .dupRule => "duplicate-rule" | .dupArgument => "duplicate-argument"
  | .incompleteArgument => "incomplete-argument"
  | .missingConflict => "missing-conflict"
  | .r1 => "R1" | .r3 => "R3" | .r4 => "R4" | .r5 => "R5" | .r6 => "R6"
  | .r7 => "R7" | .r10 => "R10" | .r11 => "R11" | .r12 => "R12" | .r13 => "R13"

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

/-- A wire attack with its endpoints still as declared argument ids. -/
inductive RawAttack where
  | rebut : String → String → RawAttack
  | undercut : String → String → Pos → RawAttack
  | undermine : String → String → Pos → RawAttack

def RawAttack.endpoints : RawAttack → String × String
  | .rebut w u => (w, u)
  | .undercut w u _ => (w, u)
  | .undermine w u _ => (w, u)

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

/-! ### Wire well-formedness invariants (R14) and endpoint resolution -/

def firstDup : List String → List String → Option String
  | [], _ => none
  | x :: rest, seen => if seen.contains x then some x else firstDup rest (x :: seen)

def lookupArg (argsRaw : List (String × SupportTerm)) (id : String) :
    Option SupportTerm :=
  (argsRaw.find? (fun e => e.1 == id)).map (·.2)

def resolveAttacks (argsRaw : List (String × SupportTerm)) :
    List RawAttack → Except String (List Attack)
  | [] => .ok []
  | ra :: rest => do
      let (s, t) := ra.endpoints
      match lookupArg argsRaw s, lookupArg argsRaw t with
      | some sw, some tw => do
          let k := (match ra with
            | .rebut _ _ => Attack.rebut sw tw
            | .undercut _ _ π => Attack.undercut sw tw π
            | .undermine _ _ π => Attack.undermine sw tw π)
          let rest' ← resolveAttacks argsRaw rest
          .ok (k :: rest')
      | _, _ => .error "attacks: attack endpoint is not a declared argument"

/-! ### Building the checker inputs -/

def buildGamma (leaves : List (LeafId × Atom)) : LeafId → Option Atom :=
  fun l => (leaves.find? (fun e => decide (e.1 = l))).map (·.2)

/-- The one implemented backend identity, `nd@1`. -/
def ndBackendId : BackendId := ⟨"nd", 1⟩

/-- Backend registry built from the wire `theories` section over `nd@1`,
mirroring `Lara.Examples.registryEx`. -/
def buildRegistry (theories : List (Digest × List Atom)) : BackendRegistry dcanon :=
  fun β =>
    if β = ndBackendId then
      some { resolve := fun h =>
        match theories.find? (fun t => decide (t.1 = h)) with
        | some t => some (Lara.Strict.ndBackendWithTheory dcanon t.2)
        | none => none }
    else none

/-- The decoded wire unit plus the derived checker inputs. Only `Type 0` data
is stored here — the backend registry (which lives in `Type 1`, since a
`Backend` carries a `Form : Type` field) is built from `theories` outside the
decode monad. -/
structure Decoded where
  policy : Policy
  args : List SupportTerm
  atts : List Attack
  gamma : LeafId → Option Atom
  theories : List (Digest × List Atom)
  queries : List Atom

/-- Peel one optional, ordered section. -/
def takeSection (t : Tag) (ss : List Sx) : Option Sx × List Sx :=
  match ss with
  | s :: rest =>
    match s with
    | .list (.atom k :: _) => if k == tagToString t then (some s, rest) else (none, ss)
    | _ => (none, ss)
  | [] => (none, ss)

def decodeUnit (e : Sx) : Except String Decoded := do
  let sections ← sectionFields "unit" .unit e
  let s0 := takeSection .policy sections
  let s1 := takeSection .theories s0.2
  let s2 := takeSection .leaves s1.2
  let s3 := takeSection .args s2.2
  let s4 := takeSection .attacks s3.2
  let s5 := takeSection .queries s4.2
  let _ ← (if s5.2.isEmpty then (.ok () : Except String _root_.Unit)
           else .error "unit: unexpected section")
  let pol ← decodePolicy s0.1
  let theories ← decodeTheories s1.1
  let leaves ← decodeLeaves s2.1
  let argsRaw ← decodeArgs s3.1
  let attacksRaw ← decodeAttacks s4.1
  let queries ← decodeQueries s5.1
  let _ ← (match firstDup (argsRaw.map (·.1)) [] with
           | some dup => (.error ("args: duplicate argument id: " ++ dup) : Except String _root_.Unit)
           | none => .ok ())
  let atts ← resolveAttacks argsRaw attacksRaw
  .ok
    { policy := { rules := pol.1, defeat := ⟨pol.2.1, pol.2.2⟩ }
    , args := argsRaw.map (·.2)
    , atts := atts
    , gamma := buildGamma leaves
    , theories := theories
    , queries := queries }

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
  | .R1 => tagToString .r1 | .R3 => tagToString .r3 | .R4 => tagToString .r4
  | .R5 => tagToString .r5 | .R6 => tagToString .r6 | .R7 => tagToString .r7
  | .R10 => tagToString .r10 | .R11 => tagToString .r11
  | .R12 => tagToString .r12 | .R13 => tagToString .r13

/-- The rejection class atom for a `checkUnit` failure — the wire `REJECTION`
vocabulary of `Lara.Wire`. -/
def rejectString : UnitError → String
  | .duplicateRule _ => tagToString .dupRule
  | .policyViolation _ => tagToString .r12
  | .program e =>
    match e with
    | .rejection _ ce => checkClassStr ce.rejectClass
    | .duplicateArgument _ _ => tagToString .dupArgument
    | .incompleteArgument _ _ => tagToString .incompleteArgument
    | .missingConflict _ => tagToString .missingConflict

def encodeReject (cls : String) : Sx :=
  .list [.atom (tagToString .verdict), .atom (tagToString .reject), .atom cls]

def encodeAccept (labels : List (Nat × Label)) (edges : List (Nat × Nat))
    (statuses : List (Atom × Status)) : Sx :=
  .list
    [ .atom (tagToString .verdict), .atom (tagToString .accept)
    , .list (.atom (tagToString .labels) ::
        labels.map (fun le => .list [sxNat le.1, .atom (labelStr le.2)]))
    , .list (.atom (tagToString .edges) ::
        edges.map (fun ij => .list [sxNat ij.1, sxNat ij.2]))
    , .list (.atom (tagToString .statuses) ::
        statuses.map (fun ps =>
          .list [.atom (tagToString .status), encodeAtom ps.1, .atom (statusStr ps.2)])) ]

/-- Read the accept verdict off an accepted unit: grounded labels over the
compiled AF (`checkedAF`), the compiled closure edges in ascending order, and
one status per query atom in query order. -/
def buildAccept {Γ : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    (accepted : Lara.Unit.CheckedUnit dcanon Γ CertOk) (queries : List Atom) : Sx :=
  let P := accepted.program
  let af := checkedAF P
  let n := P.args.length
  let labels := (List.range n).map (fun i => (i, labelC af i))
  let edges := (List.range n).foldr
    (fun i acc => (List.range n).foldr
      (fun j acc2 => if af.attack i j then (i, j) :: acc2 else acc2) acc) []
  let statuses := queries.map (fun p => (p, statusC af (completeClaimFor accepted p)))
  encodeAccept labels edges statuses

/-! ### The driver -/

def runOnContents (contents : String) : IO _root_.Unit := do
  match parseWire contents with
  | .error msg =>
      IO.eprintln ("lara-driver: codec error at " ++ msg)
      IO.Process.exit 2
  | .ok e =>
    match decodeUnit e with
    | .error msg =>
        IO.eprintln ("lara-driver: codec error at " ++ msg)
        IO.Process.exit 2
    | .ok d =>
      let reg := buildRegistry d.theories
      match checkUnit d.gamma reg
          ({ policy := d.policy, args := d.args, atts := d.atts } : Lara.Unit) with
      | .error err =>
          IO.println (printSx (encodeReject (rejectString err)))
          IO.Process.exit 1
      | .ok accepted =>
          IO.println (printSx (buildAccept accepted d.queries))

end Lara.Driver

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
      Lara.Driver.runOnContents contents
  | _ =>
      IO.eprintln "usage: lara-driver <file.sexp>"
      IO.Process.exit 2
