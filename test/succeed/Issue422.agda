
module Issue422 where

data Bool : Set where
  true false : Bool

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

foo : Bool → Bool → Bool
foo true  b    = b
foo n      true = true
foo false b    = false

good : foo false true ≡ true
good = refl

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

data T : Set where
  t₁ : Nat → T
  t₂ : Nat → Nat → T
  t₃ : Nat → Nat → Nat → T

bar : Nat → Nat → Nat → T
bar x  zero    z      = t₂ x z
bar x  y      (suc z) = t₃ x y z
bar x (suc y)  zero   = t₂ x y

postulate
  a b c : Nat

eqn₁ : bar a zero c ≡ t₂ a c
eqn₁ = refl

eqn₂ : bar a (suc b) (suc c) ≡ t₃ a (suc b) c
eqn₂ = refl

eqn₃ : bar a (suc b) zero ≡ t₂ a b
eqn₃ = refl
