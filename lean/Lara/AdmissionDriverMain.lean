import Lara.AdmissionDriver

/-- Executable wrapper for `admission-driver`: the admission differential
driver's `main` lives in the `Lara.AdmissionDriver` namespace (its imports
already provide `Lara.Driver.main`). -/
def main (args : List String) : IO _root_.Unit :=
  Lara.AdmissionDriver.main args
