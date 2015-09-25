-- Andreas, 2014-07-02 Documenting the ETA pragma

open import Common.Equality

mutual
  data Colist (A : Set) : Set where
    [] : Colist A
    _∷_ : A → ∞Colist A → Colist A

  record ∞Colist (A : Set) : Set where
    eta-equality
    coinductive
    constructor delay
    field       force : Colist A

open ∞Colist

-- By default, recursive records do not have eta,
-- but it can be turned on by force.
-- In case of colists, it is ok, since there is no
-- infinite eta-expansion (unlike for streams).

test : {A : Set} (x : ∞Colist A) → x ≡ delay (force x)
test x = refl
