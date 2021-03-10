
open import Agda.Primitive

variable
  a : Level
  A : Set a
  x : A

postulate
  P : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → Set
  p : P x

postulate
  H : ∀ a (A : Set a) (x : A) → Set
  Id : ∀ {a} (A : Set a) → A → A → Set a
  h : (i : H _ _ x) (j : H a _ _) → Id (H _ A _) i j
