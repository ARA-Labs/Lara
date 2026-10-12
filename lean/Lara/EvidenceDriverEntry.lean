/-
The `evidence-driver` executable entry point, in its own module.

`Lara.EvidenceDriver` defines `Lara.EvidenceDriver.main` inside its namespace so
that importing it (for instance from the frozen `Lara.Process.SourceWire`) never
collides with another executable's entry point. The root-level `main` that Lake
needs for `evidence-driver` therefore lives here, in a module that no library
module imports.
-/
import Lara.EvidenceDriver

/-- Executable entry point for `evidence-driver`. -/
def main (args : List String) : IO _root_.Unit :=
  Lara.EvidenceDriver.main args
