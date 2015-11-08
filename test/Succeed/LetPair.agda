-- Andreas, 2012-06-05 let for record patterns

-- {-# OPTIONS --show-implicit #-}
-- {-# OPTIONS -v tc.term.let.pattern:100 #-}
-- {-# OPTIONS -v tc.lhs.top:100 #-}

module LetPair where

import Common.Level
open import Common.Equality

infixl 6 _×_
infixl 0 _,_

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B
open _×_

swap : {A B : Set} → A × B → B × A
swap p =
  let (a , b) = p
  in  (b , a)

prop_swap : {A B : Set}{p : A × B} →
  (fst (swap p) ≡ snd p) ×
  (snd (swap p) ≡ fst p)
prop_swap = refl , refl

rot3 : {A B C : Set} → A × B × C → B × C × A
rot3 = λ t → let
      a , b , c = t
  in  b , c , a

postulate
  A B C : Set

rot3' = λ t → let
      x : A × B × C
      x = t
      a , b , c = x
  in  b , c , a

record ⊤ : Set where
  constructor tt

test = let tt , _ = tt , tt in A

