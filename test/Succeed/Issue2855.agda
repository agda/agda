{-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

test : (x y : Nat) → x ≡ y → x ≡ 1 → y ≡ 1 → Nat
test (suc zero) (suc zero) refl refl refl = {!!}
