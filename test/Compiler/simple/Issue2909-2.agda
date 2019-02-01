{-# OPTIONS --guardedness #-}

open import Agda.Builtin.Coinduction
open import Agda.Builtin.IO
open import Agda.Builtin.Unit

data D : Set where
  c : ∞ D → D

d : D
d = c (♯ d)

postulate
  seq    : {A B : Set} → A → B → B
  return : {A : Set} → A → IO A

{-# COMPILE GHC return = \_   -> return #-}
{-# COMPILE GHC seq    = \_ _ -> seq    #-}

main : IO ⊤
main = seq d (return tt)
