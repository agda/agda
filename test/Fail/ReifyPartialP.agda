module ReifyPartialP where

open import Agda.Primitive
open import Agda.Primitive.Cubical

postulate
  A : Set
  B : A → Set

module _ (φ : I) (a a' : Partial φ A)  where
  _ : PartialP {lzero} φ (λ { (φ = i1) → B (a itIsOne) }) → Set
  _ = λ x → x

-- error message should display a PartialP
-- even if the system is a bit mangled (as per usual)
