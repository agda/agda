module QualifiedDo where

module X where postulate
  M     : Set → Set
  _>>=_ : ∀ {A B} → M A → (A → M B) → M B
  _>>_  : ∀ {A B} → M A → M B → M B
  pure  : ∀ {A} → A → M A

module Y where postulate
  N     : Set → Set
  _>>=_ : ∀ {A B} → N A → (A → N B) → N B
  pure  : ∀ {A} → A → N A
  toM   : ∀ {A} → N A → X.M A

open X
open Y using (N ; toM)

postulate
  A B C D : Set
  a : A
  f : A → N B
  g : B → N C
  h i : C → M D

test : M D
test = do
  -- this arrow refers to X._>>=_
  x ← toM Y.do
    -- this arrow refers to Y._>>=_
    y ← f a
    g y
  -- and out here we're back to using X._>>_
  h x
  i x
