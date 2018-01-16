
open import Common.Prelude
open import Common.Equality

infixr 5 _∷_

data Vec (A : Set) : Nat → Set where
  [] : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

record Eq (A : Set) : Set where
  field
    _==_ : (x y : A) → Maybe (x ≡ y)

open Eq {{...}}

data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (x : A) → B x → Σ A B

eqNat : (n m : Nat) → Maybe (n ≡ m)
eqNat zero zero = just refl
eqNat zero (suc m) = nothing
eqNat (suc n) zero = nothing
eqNat (suc n) (suc m) with eqNat n m
eqNat (suc n) (suc m) | nothing = nothing
eqNat (suc n) (suc .n) | just refl = just refl

eqVec : ∀ {A n} {{EqA : Eq A}} (xs ys : Vec A n) → Maybe (xs ≡ ys)
eqVec [] [] = just refl
eqVec (x ∷ xs) ( y ∷  ys) with x == y    | eqVec xs ys
eqVec (x ∷ xs) ( y ∷  ys)    | nothing   | _         = nothing
eqVec (x ∷ xs) ( y ∷  ys)    | _         | nothing   = nothing
eqVec (x ∷ xs) (.x ∷ .xs)    | just refl | just refl = just refl

eqSigma : ∀ {A B} {{EqA : Eq A}} {{EqB : ∀ {x} → Eq (B x)}} (x y : Σ A B) → Maybe (x ≡ y)
eqSigma (x , y) (x₁ , y₁) with x == x₁
eqSigma (x , y) (x₁ , y₁) | nothing = nothing
eqSigma (x , y) (.x , y₁) | just refl with y == y₁
eqSigma (x , y) (.x , y₁) | just refl | nothing = nothing
eqSigma (x , y) (.x , .y) | just refl | just refl = just refl

instance
  EqNat : Eq Nat
  EqNat = record { _==_ = eqNat }

  EqVec : ∀ {A n} {{_ : Eq A}} → Eq (Vec A n)
  EqVec = record { _==_ = eqVec }

  EqSigma : ∀ {A B} {{_ : Eq A}} {{_ : ∀ {x} → Eq (B x)}} → Eq (Σ A B)
  EqSigma = record { _==_ = eqSigma }

cmpSigma : (xs ys : Σ Nat (Vec Nat)) → Maybe (xs ≡ ys)
cmpSigma xs ys = xs == ys
