{-# OPTIONS --cubical #-}

open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Unit

postulate
  F :
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    tt ≡ tt

-- The isRigid test in checkArgumentsE' does not (at the time of
-- writing) treat tt ≡ tt as rigid.

_ = F
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
