{-# OPTIONS --no-fast-reduce #-}
open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

foo : Nat → Nat
foo 1_000_000 = 1
foo (suc (suc n)) = n
foo _ = 0

_ : foo 1_000_000 ≡ 1
_ = refl

_ : foo 999_999 ≡ 999_997
_ = refl

_ : foo 1 ≡ 0
_ = refl

bar : Nat → Nat
bar 3 = 0
bar 2 = 1
bar _ = 2

_ : ∀ x → bar (suc (suc (suc (suc x)))) ≡ 2
_ = λ x → refl
