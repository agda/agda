module Issue8242 where

open import Agda.Builtin.Unit

module B (a : ⊤) where
  record C : Set where
    field
      f : ⊤

module X = B tt

-- record type is only copied by virtue of copying the proper projection which lives in the record module
--   so if we inherit the module from the projection when choosing where to put the record
open B tt using (module C)

postulate c : X.C

open C c

