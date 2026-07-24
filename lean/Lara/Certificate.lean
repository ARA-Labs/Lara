/-
Shared symbolic certificate identifiers.

This tiny module sits below both `Lara.Strict` and `Lara.Support`: the abstract
backend must consume the exact certificate reference submitted at the source
boundary, while the support calculus must carry that same closed identifier
without introducing an import cycle.
-/

namespace Lara.Support

/-- Opaque strict-certificate reference (`kappa`). The payload is never
inspected by the source calculus — only handed to backend replay. -/
structure CertRef where
  payload : String
deriving DecidableEq

end Lara.Support
