module IntroCoverageFallback where

open import Agda.Builtin.Nat

data TwoIndexes : Nat → Nat → Set₀ where
 a00 : TwoIndexes zero zero
 a10 : TwoIndexes (suc zero) zero
 a01 : TwoIndexes zero (suc zero)
 a11 : TwoIndexes (suc zero) (suc zero)

fooTI : TwoIndexes zero {!!}
fooTI = {!!}

