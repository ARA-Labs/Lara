; A map check-input declaring no members. The envelope is terminal input,
; so its own decoder settles emptiness rather than leaving it to a linker.
(map-check-input@1
  (policy empirical-v1)
  (backends (backend nd 1))
  (members)
  (alignments))
