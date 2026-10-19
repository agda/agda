{-# OPTIONS --erasure --safe #-}

open import Agda.Builtin.IO
open import Agda.Builtin.Unit

data ⊥ : Set where

-- One might think that one could allow main to take erased arguments,
-- but this is not safe in the presence of erased matches for the
-- empty type (which are at the time of writing always allowed in
-- Agda).

main : @0 ⊥ → IO ⊤
main ()
