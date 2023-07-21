{-# OPTIONS --cubical #-}
module Issue6725 where

open import Agda.Primitive
open import Agda.Builtin.Cubical.Path

variable
  ℓ : Level
  A : Set

data 𝕀 : Set where
  zero one : 𝕀
  seg : zero ≡ one

record R : Set₂ where
  field
    Φ : Set₁
    ze : Φ
    on : Φ
    se : ze ≡ on

record C : Set₂ where
  field
    Φ : 𝕀 -> Set₁
    ze : Φ zero
    on : Φ one
    se : PathP (λ i → Φ (seg i)) ze on

-- implementation doesn't matter
rec : (a : R) -> 𝕀 -> R.Φ a
rec a = ?

case : (a : C) -> (i : 𝕀) -> C.Φ a i
-- replacing this definition with a ? avoids the problem
case a = λ where
    zero -> ze
    one  -> on
    (seg i) -> se i
  where open C a

whoa : 𝕀 -> 𝕀 -> Set
whoa = rec alg where
  open R
  open C

  alg : R
  alg .Φ = 𝕀 -> Set
  alg .ze = case λ where
    .Φ _ → Set
  alg .on = case λ where
    .Φ _ → Set
  -- commenting this case avoids the problem
  alg .se i = case λ where
    .Φ _ → {!!}
    .ze → ?
    .on → ?
