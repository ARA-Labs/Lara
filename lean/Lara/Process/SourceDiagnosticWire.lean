import Lara.Process.SourceWire
import Lara.PW.Wire

namespace Lara.Process.Source.ResultWire

open Lara.Support
abbrev Sx := Driver.Sx

def encodeNat (n : Nat) : Sx := .atom (Nat.repr n)
def decodeNat : Sx → Option Nat
  | .atom s => ND.decodeNat s
  | _ => none
@[simp] theorem decode_encodeNat (n : Nat) : decodeNat (encodeNat n) = some n := by
  simp [decodeNat, encodeNat]

def encodeText (s : String) : Sx := .atom s
def decodeText : Sx → Option String
  | .atom s => some s
  | _ => none
@[simp] theorem decode_encodeText (s : String) : decodeText (encodeText s) = some s := rfl

def encodeList (encode : α → Sx) (xs : List α) : Sx := .list (xs.map encode)
def decodeList (decode : Sx → Option α) : Sx → Option (List α)
  | .list xs => Wire.decodeList decode xs
  | _ => none
@[simp] theorem decode_encodeList (encode : α → Sx) (decode : Sx → Option α)
    (h : ∀ a, decode (encode a) = some a) (xs : List α) :
    decodeList decode (encodeList encode xs) = some xs := by
  simp [decodeList, encodeList, Wire.decodeList_map, h]

def encodePair (ea : α → Sx) (eb : β → Sx) (p : α × β) : Sx := .list [ea p.1, eb p.2]
def decodePair {α β : Type} (da : Sx → Option α) (db : Sx → Option β) : Sx → Option (α × β)
  | .list [a, b] => do return (← da a, ← db b)
  | _ => none
@[simp] theorem decode_encodePair (ea : α → Sx) (eb : β → Sx)
    (da : Sx → Option α) (db : Sx → Option β)
    (ha : ∀ a, da (ea a) = some a) (hb : ∀ b, db (eb b) = some b) (p : α × β) :
    decodePair da db (encodePair ea eb p) = some p := by
  cases p; simp [encodePair, decodePair, ha, hb]

abbrev encodeAtom := PW.Wire.encodeAtom
def decodeAtom (s : Sx) : Option Atom := (PW.Wire.decodeAtom s).toOption
@[simp] theorem decode_encodeAtom (a : Atom) : decodeAtom (encodeAtom a) = some a := by
  simp [decodeAtom, encodeAtom, Except.toOption]
abbrev encodeTerm := PW.Wire.encodeTerm
def decodeTerm (s : Sx) : Option Term := (PW.Wire.decodeTerm s).toOption
@[simp] theorem decode_encodeTerm (a : Term) : decodeTerm (encodeTerm a) = some a := by
  simp [decodeTerm, encodeTerm, Except.toOption]
abbrev encodeStatus := PW.Wire.encodeStatus
def decodeStatus (s : Sx) : Option Grounded.Status := (PW.Wire.decodeStatus s).toOption
@[simp] theorem decode_encodeStatus (a : Grounded.Status) : decodeStatus (encodeStatus a) = some a := by
  simp [decodeStatus, encodeStatus, Except.toOption]

/-- Core syntax uses the production Driver spelling, not a new term grammar. -/
def coreNode (tag : Driver.Tag) (xs : List Sx) : Sx := .list (.atom (Driver.tagToString tag) :: xs)

mutual
  def encodePat : Pat → Sx
    | .var x => coreNode .var [.atom x.name]
    | .num s => coreNode .numLit [.atom s]
    | .str s => coreNode .strLit [.atom s]
    | .con k ps => coreNode .conApp (.atom k.name :: encodePats ps)
  def encodePats : Pats → List Sx
    | .nil => []
    | .cons p ps => encodePat p :: encodePats ps
end
mutual
  def decodePat : Sx → Option Pat
    | .list (.atom tag :: args) =>
      if tag = Driver.tagToString .var then
        match args with | [.atom s] => some (.var ⟨s⟩) | _ => none
      else if tag = Driver.tagToString .numLit then
        match args with | [.atom s] => some (.num s) | _ => none
      else if tag = Driver.tagToString .strLit then
        match args with | [.atom s] => some (.str s) | _ => none
      else if tag = Driver.tagToString .conApp then
        match args with | .atom k :: ps => do return .con ⟨k⟩ (← decodePats ps) | _ => none
      else none
    | _ => none
  termination_by wire => sizeOf wire
  def decodePats : List Sx → Option Pats
    | [] => some .nil
    | p :: ps => do return .cons (← decodePat p) (← decodePats ps)
  termination_by wires => sizeOf wires
end
mutual
  @[simp] theorem decode_encodePat (p : Pat) : decodePat (encodePat p) = some p := by
    cases p with
    | var x => simp [encodePat, decodePat, coreNode, Driver.tagToString]
    | num s => simp [encodePat, decodePat, coreNode, Driver.tagToString]
    | str s => simp [encodePat, decodePat, coreNode, Driver.tagToString]
    | con k ps =>
        cases ps <;> simp [encodePat, encodePats, decodePat, decodePats, coreNode,
          Driver.tagToString, decode_encodePat, decode_encodePats]
  @[simp] theorem decode_encodePats (ps : Pats) : decodePats (encodePats ps) = some ps := by
    cases ps <;> simp [encodePats, decodePats, decode_encodePat, decode_encodePats]
end

def encodeAPat (a : APat) : Sx := coreNode .apat (.atom a.pred.name :: encodePats a.args)
def decodeAPat : Sx → Option APat
  | .list (.atom tag :: .atom pred :: ps) =>
    if tag = Driver.tagToString .apat then do return ⟨⟨pred⟩, ← decodePats ps⟩ else none
  | _ => none
@[simp] theorem decode_encodeAPat (a : APat) : decodeAPat (encodeAPat a) = some a := by
  cases a; simp [encodeAPat, decodeAPat, coreNode]

mutual
  def encodeSExpr : SExpr → Sx
    | .atom s => .atom s
    | .list xs => .list (encodeSExprs xs)
  def encodeSExprs : List SExpr → List Sx
    | [] => []
    | x :: xs => encodeSExpr x :: encodeSExprs xs
end
mutual
  def decodeSExpr : Sx → SExpr
    | .atom s => .atom s
    | .list xs => .list (decodeSExprs xs)
  def decodeSExprs : List Sx → List SExpr
    | [] => []
    | x :: xs => decodeSExpr x :: decodeSExprs xs
end
mutual
  @[simp] theorem decode_encodeSExpr (a : SExpr) : decodeSExpr (encodeSExpr a) = a := by
    cases a <;> simp [encodeSExpr, decodeSExpr, decode_encodeSExprs]
  @[simp] theorem decode_encodeSExprs (xs : List SExpr) : decodeSExprs (encodeSExprs xs) = xs := by
    cases xs <;> simp [encodeSExprs, decodeSExprs, decode_encodeSExpr, decode_encodeSExprs]
end

def encodeCertRef (c : CertRef) : Sx := encodeSExpr c.payload
def decodeCertRef (s : Sx) : Option CertRef := some ⟨decodeSExpr s⟩
@[simp] theorem decode_encodeCertRef (c : CertRef) : decodeCertRef (encodeCertRef c) = some c := by
  cases c; simp [decodeCertRef, encodeCertRef]

def encodeAssurance : Assurance → Sx
  | .none => .atom (Driver.tagToString .nonE)
  | .trusted => .atom (Driver.tagToString .trusted)
  | .cert b d c => coreNode .cert [.atom b.name, encodeNat b.version, .atom d.hash, encodeCertRef c]
def decodeAssurance : Sx → Option Assurance
  | .atom s => if s = Driver.tagToString .nonE then some .none else
      if s = Driver.tagToString .trusted then some .trusted else none
  | .list [.atom tag, .atom b, n, .atom d, c] =>
      if tag = Driver.tagToString .cert then do
        return .cert ⟨b, ← decodeNat n⟩ ⟨d⟩ (← decodeCertRef c)
      else none
  | _ => none
@[simp] theorem decode_encodeAssurance (a : Assurance) :
    decodeAssurance (encodeAssurance a) = some a := by
  cases a <;> simp [encodeAssurance, decodeAssurance, coreNode, Driver.tagToString]

def encodeVar (x : VarId) : Sx := .atom x.name
def decodeVar : Sx → Option VarId
  | .atom s => some ⟨s⟩
  | _ => none
@[simp] theorem decode_encodeVar (x : VarId) : decodeVar (encodeVar x) = some x := rfl

def encodeQuestion (x : QuestionId) : Sx := .atom x.name
def decodeQuestion : Sx → Option QuestionId
  | .atom s => some ⟨s⟩
  | _ => none
@[simp] theorem decode_encodeQuestion (x : QuestionId) : decodeQuestion (encodeQuestion x) = some x := rfl

def encodeSubst (s : Subst) : Sx := coreNode .subst (s.map (encodePair encodeVar encodeTerm))
def decodeSubst : Sx → Option Subst
  | .list (.atom tag :: xs) => if tag = Driver.tagToString .subst then
      Wire.decodeList (decodePair decodeVar decodeTerm) xs else none
  | _ => none
@[simp] theorem decode_encodeSubst (s : Subst) : decodeSubst (encodeSubst s) = some s := by
  simp [encodeSubst, decodeSubst, coreNode, Wire.decodeList_map]

mutual
  def encodeSupport : SupportTerm → Sx
    | .leaf l => coreNode .leaf [.atom l.name]
    | .inst r s ps ds hs a => coreNode .inst [.atom r.name, encodeSubst s,
        coreNode .premises (encodeSupports ps), coreNode .discharges (encodeDischarges ds),
        coreNode .holes (hs.map encodeQuestion), coreNode .assurance [encodeAssurance a]]
  def encodeSupports : List SupportTerm → List Sx
    | [] => []
    | x :: xs => encodeSupport x :: encodeSupports xs
  def encodeDischarges : List (QuestionId × SupportTerm) → List Sx
    | [] => []
    | (q, w) :: xs => .list [encodeQuestion q, encodeSupport w] :: encodeDischarges xs
end
mutual
  def decodeSupport : Sx → Option SupportTerm
    | .list [.atom tag, .atom l] => if tag = Driver.tagToString .leaf then some (.leaf ⟨l⟩) else none
    | .list [.atom tag, .atom r, s, .list (.atom pt :: ps), .list (.atom dt :: ds),
        .list (.atom ht :: hs), .list [.atom atag, a]] =>
      if tag = Driver.tagToString .inst ∧ pt = Driver.tagToString .premises ∧
          dt = Driver.tagToString .discharges ∧ ht = Driver.tagToString .holes ∧
          atag = Driver.tagToString .assurance then do
        return .inst ⟨r⟩ (← decodeSubst s) (← decodeSupports ps) (← decodeDischarges ds)
          (← Wire.decodeList decodeQuestion hs) (← decodeAssurance a)
      else none
    | _ => none
  termination_by wire => sizeOf wire
  def decodeSupports : List Sx → Option (List SupportTerm)
    | [] => some []
    | x :: xs => do return (← decodeSupport x) :: (← decodeSupports xs)
  termination_by wires => sizeOf wires
  def decodeDischarges : List Sx → Option (List (QuestionId × SupportTerm))
    | [] => some []
    | .list [.atom q, w] :: xs => do return (⟨q⟩, ← decodeSupport w) :: (← decodeDischarges xs)
    | _ => none
  termination_by wires => sizeOf wires
end
mutual
  @[simp] theorem decode_encodeSupport (w : SupportTerm) : decodeSupport (encodeSupport w) = some w := by
    cases w <;> simp [encodeSupport, decodeSupport, coreNode, Driver.tagToString,
      decode_encodeSupports, decode_encodeDischarges, Wire.decodeList_map]
  @[simp] theorem decode_encodeSupports (ws : List SupportTerm) :
      decodeSupports (encodeSupports ws) = some ws := by
    cases ws <;> simp [encodeSupports, decodeSupports, decode_encodeSupport, decode_encodeSupports]
  @[simp] theorem decode_encodeDischarges (ds : List (QuestionId × SupportTerm)) :
      decodeDischarges (encodeDischarges ds) = some ds := by
    cases ds with
    | nil => simp [encodeDischarges, decodeDischarges]
    | cons d ds => cases d; simp [encodeDischarges, decodeDischarges, encodeQuestion,
        decode_encodeSupport, decode_encodeDischarges]
end

end Lara.Process.Source.ResultWire
