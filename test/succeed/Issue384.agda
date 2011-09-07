
module Issue384 where

postulate
  D : (A : Set) → A → Set

data I : Set where
  i : I

D′ : (A : Set) → A → I → Set
D′ A x i = D A x

postulate
  Q : (A : Set) → A → Set
  q : ∀ j A (x : A) → D′ A x j → Q A x

  A : Set
  x : A
  d : D A x

  P : (A : Set) → A → Set
  p : P (Q _ _) (q _ _ _ d)
