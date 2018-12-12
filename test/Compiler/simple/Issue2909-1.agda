{-# OPTIONS --guardedness #-}

open import Agda.Builtin.IO
open import Agda.Builtin.Unit

record Box (A : Set) : Set where
  field
    unbox : A

open Box public

record R : Set where
  coinductive
  field
    force : Box R

open R public

r : R
unbox (force r) = r

postulate
  seq    : {A B : Set} → A → B → B
  return : {A : Set} → A → IO A

{-# COMPILE GHC return = \_   -> return #-}
{-# COMPILE GHC seq    = \_ _ -> seq    #-}

main : IO ⊤
main = seq r (return tt)
