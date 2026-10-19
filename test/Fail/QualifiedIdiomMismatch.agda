module QualifiedIdiomMismatch where

module Y where postulate
  N     : Set → Set
  _<*>_ : ∀ {A B} → N (A → B) → N A → N B
  pure  : ∀ {A} → A → N A

open Y using (N)

postulate
  A B C : Set
  a : N A
  b : N B
  f : A → B → C

test2 : N C
test2 = Y.⦇ f a b |)
