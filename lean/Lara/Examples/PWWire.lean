import Lara.PW.Wire

namespace Lara.Examples.PWWire
open Lara Lara.PW.Surface Lara.PW.Wire

-- The fixture keeps duplicates and a shadowed entry, which the codec must preserve.
def bridge : BridgeDecl :=
  ⟨⟨"b"⟩, ⟨"src"⟩, ⟨"dst"⟩,
    [.pred ⟨"p"⟩ ⟨"q"⟩, .con ⟨"c"⟩ ⟨"d"⟩, .pred ⟨"p"⟩ ⟨"shadowed"⟩],
    [⟨⟨"l"⟩, ⟨"m"⟩⟩], [.leafOk, .ruleOk, .certOk]⟩

def claim : Atom := .atom "p" (.cons (.num "01.00")
  (.cons (.str "quote\" slash\\ newline\n 世界") (.cons (.con "c" .nil) .nil)))

def doc : Document := ⟨[bridge, bridge],
  [⟨⟨"src"⟩, .conj (.neg .top) (.box ⟨"b"⟩ (.dia ⟨"b"⟩ (.status .justified claim)))⟩,
   ⟨⟨"dst"⟩, .status .contested claim⟩, ⟨⟨"dst"⟩, .status .defeated claim⟩,
   ⟨⟨"dst"⟩, .status .gap claim⟩]⟩

example : decodeDocument (encodeDocument doc) = .ok doc := decodeDocument_encode doc

/-- Text tests are executable boundary evidence, not extra axioms. -/
def assertRoundTrip (d : Document) : IO _root_.Unit :=
  match parse (print d) with
  | .error e => throw (IO.userError s!"round trip rejected: {e.tag.text}: {e.detail}")
  | .ok decoded => unless decoded = d do throw (IO.userError "round trip changed AST")

def assertError (input : String) (expected : ErrorTag) : IO _root_.Unit :=
  match parse input with
  | .ok _ => throw (IO.userError s!"unexpected acceptance: {input}")
  | .error e => unless e.tag = expected do
    throw (IO.userError s!"wrong category: {e.tag.text}, expected {expected.text}: {input}")

/-- Exercise arbitrary identifier/literal text in each named namespace. -/
def textDoc (text : String) : Document :=
  ⟨[⟨⟨text⟩, ⟨text⟩, ⟨text⟩,
      [.pred ⟨text⟩ ⟨text⟩, .con ⟨text⟩ ⟨text⟩],
      [⟨⟨text⟩, ⟨text⟩⟩], [.certOk, .leafOk, .ruleOk, .leafOk]⟩],
    [⟨⟨text⟩, .box ⟨text⟩ (.status .gap
      (.atom text (.cons (.num text) (.cons (.str text)
        (.cons (.con text (.cons (.con text .nil) .nil)) .nil)))))⟩]⟩

def tests : IO _root_.Unit := do
  assertRoundTrip doc
  assertRoundTrip ⟨[], []⟩
  for text in ["", "ordinary", "1", "(a);b", "quote\"", "slash\\", "line\nnext",
      "tab\treturn\r", "世界 λ 🧪", String.singleton (Char.ofNat 0)] do
    assertRoundTrip (textDoc text)
  unless print ⟨[], []⟩ = "(pw-surface 1 (bridges) (queries))" do
    throw (IO.userError "canonical empty document changed")
  let canonical : Document := ⟨[bridge],
    [⟨⟨"src"⟩, .box ⟨"b"⟩ (.status .justified (.atom "p" (.cons (.num "01.00") .nil)))⟩]⟩
  unless print canonical = "(pw-surface 1 (bridges (bridge b src dst (symbols (pred p q) (con c d) (pred p shadowed)) (leaves (leaf l m)) (clauses leaf-ok rule-ok cert-ok))) (queries (pose src (box b (status justified (atom p (num 01.00)))))))" do
    throw (IO.userError "canonical declaration/query encoding changed")
  match parse "; comment\n(pw-surface 1 (bridges) ; section\n (queries)) ; end" with
  | .ok d => unless d = ⟨[], []⟩ do throw (IO.userError "comment parse changed AST")
  | .error _ => throw (IO.userError "comments rejected")
  for input in ["", "(", "\"unterminated", "\"bad\\q\"",
      "(pw-surface 1 (bridges) (queries)) extra", "() ()", ")"] do
    assertError input .syntax
  for version in ["0", "2", "01", "future"] do
    assertError s!"(pw-surface {version} (bridges) (queries))" .unsupportedVersion
  -- A later version is recognized whatever section layout it uses.
  for input in ["(pw-surface 2 (bridges) (queries) (worlds))", "(pw-surface 2)",
      "(pw-surface 2 (queries) (bridges))"] do
    assertError input .unsupportedVersion
  for input in ["x", "()", "(pw-surface)", "(pw-surface (1) (bridges) (queries))",
      "(other 1 (bridges) (queries))",
      "(pw-surface 1 (bridges))", "(pw-surface 1 (bridges) (queries) extra)",
      "(pw-surface 1 (queries) (bridges))",
      "(pw-surface 1 (bridges (bridge b src dst)) (queries))",
      "(pw-surface 1 (bridges (bridge b src dst (symbols) (leaves) (clauses) extra)) (queries))",
      "(pw-surface 1 (bridges (bridge b src dst (symbols (pred p)) (leaves) (clauses))) (queries))",
      "(pw-surface 1 (bridges (bridge b src dst (symbols (unknown p q)) (leaves) (clauses))) (queries))",
      "(pw-surface 1 (bridges (bridge b src dst (symbols) (leaves (leaf l m extra)) (clauses))) (queries))",
      "(pw-surface 1 (bridges (bridge b src dst (symbols) (leaves) (clauses wrong))) (queries))",
      "(pw-surface 1 (bridges) (queries (pose src)))"] do
    assertError input .malformed
  for formula in ["(top extra)", "(not)", "(and (top))", "(box b)",
      "(dia b (top) extra)", "(status unknown (atom p))", "(status gap)",
      "(status gap (atom))", "(status gap (atom p (num)))",
      "(status gap (atom p (str x y)))", "(status gap (atom p (con)))",
      "(unknown)"] do
    assertError s!"(pw-surface 1 (bridges) (queries (pose src {formula})))" .malformed

#eval tests
end Lara.Examples.PWWire
