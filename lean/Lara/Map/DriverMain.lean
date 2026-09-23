import Lara.Map.Driver

/-- Executable wrapper for `lara-map-driver`: the map driver's `main` lives in
the `Lara.Map.Driver` namespace so that importing the module never collides with
another executable's entry point. -/
def main (args : List String) : IO _root_.Unit :=
  Lara.Map.Driver.main args
