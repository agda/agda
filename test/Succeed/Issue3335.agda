{-# OPTIONS --rewriting --confluence-check #-}

open import Agda.Builtin.Equality
{-# BUILTIN REWRITE _≡_ #-}

record Box (P : Set) : Set where
  constructor box
  field
    unbox : P
open Box public

postulate
  A : Set
  a : A
  f : Box A → A
  f= : f (box a) ≡ a
{-# REWRITE f= #-}

[a] : Box A
unbox [a] = a

-- Works thanks to eta
test1 : [a] ≡ box a
test1 = refl

-- Should work as well
test2 : f [a] ≡ f (box a)
test2 = refl
