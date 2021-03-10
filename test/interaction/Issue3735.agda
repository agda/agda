
open import Agda.Primitive

variable
  a : Level

postulate
  works : Set a → {a : Set} → a
  fails : Set a → {a : Set} → {!a!}

module _ (A : Set a) (a : A) where
  x : A
  x = a
