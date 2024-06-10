
module _ where

open import Agda.Primitive
open import Agda.Builtin.List
open import Agda.Builtin.Nat

variable
  l : Level
  A : Set l

postulate
  HasSize : Set l → Set l
  sizeOf  : ⦃ HasSize A ⦄ → A → Nat

  instance
    HasSizeList : HasSize (List A)

  IsShort : Nat → Set

  foo : (xs : List A) → IsShort (sizeOf xs) → Nat
