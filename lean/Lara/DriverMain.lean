import Lara.Driver

/-- Executable wrapper for `lara-driver`: the wire driver's `main` lives in
the `Lara.Driver` namespace so that importing the module never collides with
another executable's entry point. -/
def main (args : List String) : IO _root_.Unit :=
  Lara.Driver.main args
