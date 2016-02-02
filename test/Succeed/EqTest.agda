module EqTest where

import Common.Level

open import Common.Maybe
open import Common.Equality

data ℕ : Set where
  zero : ℕ
  suc  : ℕ -> ℕ

_≟_ : (x y : ℕ) -> Maybe (x ≡ y)
suc m  ≟ suc n with m ≟ n
suc .n ≟ suc n |    just refl = just refl
suc m  ≟ suc n |    nothing   = nothing
zero   ≟ suc _ = nothing
suc m  ≟ zero  = nothing
zero   ≟ zero  = just refl
