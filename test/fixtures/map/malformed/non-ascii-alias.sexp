; A member alias that is NON-ASCII, written as a QUOTED atom.
;
; The quoting is the whole point. A bare non-ASCII atom never reaches the alias
; check at all -- both drivers' S-expression lexers restrict a bare atom to
; printable ASCII, so it dies as a parse error and tests nothing about aliases.
; A quoted atom parses, so this is the only shape that actually exercises the
; rule: an alias is nonempty ASCII [A-Za-z0-9_-], which is what keeps it clear
; of the `:` that frames a qualified key and inside the bare-atom set so no
; verdict byte needs quoting for it.
;
; Both decoders must refuse it, and their two spellings of the rule are
; independent -- Haskell's `isAscii c && isAlphaNum c` against Lean's
; `Char.isAlphanum`, which agree only because the latter is ASCII-only.
(map-check-input@1
  (policy empirical-v1)
  (backends (backend nd 1))
  (members
    (member "café" m.lara (artifact sha256:m) (claims (claim c1 (atom p (con a)))) (unit (sigma (sorts S) (cons (con a (args) S) (con b (args) S)) (preds (pred p (args S)) (pred q (args S)))) (policy (rules) (contraries) (exceptions)))))
  (alignments))
