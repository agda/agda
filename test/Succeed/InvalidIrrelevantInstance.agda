open import Agda.Builtin.Equality
open import Agda.Builtin.FromNat
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Agda.Primitive renaming (Set to Type)

is-prop : ∀ {ℓ} → Type ℓ → Type ℓ
is-prop T = (x y : T) → x ≡ y

is-hlevel : ∀ {ℓ} → Type ℓ → Nat → Type _
is-hlevel A 0       = is-prop A
is-hlevel A (suc n) = (x y : A) → is-hlevel (_≡_ {A = A} x y) n

postulate
  H-Level : ∀ {ℓ} (T : Type ℓ) (n : Nat) → Type ℓ
  hlevel : ∀ {ℓ} {T : Type ℓ} n ⦃ x : H-Level T n ⦄ → is-hlevel T n

instance
  Number-Nat : Number Nat
  Number-Nat .Number.Constraint _ = ⊤
  Number-Nat .Number.fromNat n = n

data ⊥ : Type where

postulate instance
  t2 : H-Level ⊤ 0
  t1 : H-Level ⊥ 0

postulate foo : .(is-prop ⊥) → ⊤

bar : ⊤
bar = foo (hlevel 0)
