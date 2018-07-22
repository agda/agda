-- Andreas, 2018-07-22, issue #3136
-- WAS: Internal error when printing termination errors

{-# OPTIONS --postfix-projections #-}

module Issue3136 (A : Set) where

-- postulate A : Set
postulate
  any : {X : Set} → X
  x : A
  P : A → Set

record C : Set where
  field
    a : A
    b : P a

c : C
c = λ where
  .C.a → x
  .C.b → λ where
    → any

-- Should report a termination error but not crash
