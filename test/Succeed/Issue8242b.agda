module Issue8242b where

module Issue8242 where

open import Agda.Builtin.Unit

module B (a : ⊤) where
  record C : Set where
    field
      f : ⊤

  -- variant of Issue8242 where the module that actually contains the
  -- proper projection that gets copied is in a nested module with some
  -- intervening parameters
  module N1 (a : ⊤) where
    module N2 where
      module N3 = C renaming (f to g) using ()

module X = B tt

open B tt using (module N1)

postulate c : X.C

open N1.N2.N3 tt c

