{-# OPTIONS --guardedness-preserving-type-constructors #-}

open import Agda.Builtin.Coinduction
open import Agda.Builtin.IO
open import Agda.Builtin.Unit

data Rec (A : ∞ Set) : Set where
  fold : ♭ A → Rec A

D : Set
D = Rec (♯ (∞ D))

d : D
d = fold (♯ d)

postulate
  seq    : {A B : Set} → A → B → B
  return : {A : Set} → A → IO A

{-# COMPILE GHC return = \_   -> return #-}
{-# COMPILE GHC seq    = \_ _ -> seq    #-}

main : IO ⊤
main = seq d (return tt)
