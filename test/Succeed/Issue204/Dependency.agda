module Issue204.Dependency where

open import Common.Level public renaming (lsuc to suc)

record R (ℓ : Level) : Set (suc ℓ) where

data D (ℓ : Level) : Set (suc ℓ) where

module M {ℓ : Level} (d : D ℓ) where
