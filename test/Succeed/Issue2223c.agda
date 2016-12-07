
module _ where

open import Agda.Primitive

module _ (a ℓ ℓ' : Level) where

  mutual
    X : Level
    X = _  -- Agda 2.5.1.1 solves this level meta

    hyp : Set₁
    hyp with (lsuc ℓ')
    ... | _ = Set
      where
        X<=a : Set (X ⊔ a) → Set a
        X<=a A = A

    test : Set₁
    test with (lsuc ℓ)
    ... | _ = Set
      where
        a<=X : Set (X ⊔ a) → Set X
        a<=X A = A
