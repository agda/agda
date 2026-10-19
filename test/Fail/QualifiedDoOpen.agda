module QualifiedDoOpen where

module X where postulate
  M     : Set → Set
  _>>=_ : ∀ {A B} → M A → (A → M B) → M B
  pure  : ∀ {A} → A → M A

module Y where postulate
  N     : Set → Set
  _>>=_ : ∀ {A B} → N A → (A → N B) → N B
  pure  : ∀ {A} → A → N A

open X
open Y using (N)

postulate
  A : Set
  a : A

-- qualified do does not open the qualifying module
test2 : N A
test2 = Y.do
  x ← Y.pure a
  Y.pure x >>= λ _ → Y.pure x
  -- M _ !<= N A
