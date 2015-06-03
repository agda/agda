open import Common.Equality
open import Common.Prelude hiding (pred)

pred : Nat → Nat
pred = _∸ 1

T : Bool → Set
T = if_then ⊤ else ⊥

if : {A : Set} (b : Bool) → A → A → A
if b = if b then_else_

test₁ : Nat → Nat
test₁ = 5 +_

test₁-test : ∀ x → test₁ x ≡ 5 + x
test₁-test _ = refl

test₂ : Nat → Nat
test₂ = _* 5

test₂-test : ∀ x → test₂ x ≡ x * 5
test₂-test _ = refl

infixr 9 _∘_

_∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
f ∘ g = λ x → f (g x)

test₃ : Nat → Nat
test₃ = (_* 5) ∘ (6 +_) ∘ (2 ∸_)

test₃-test : ∀ x → test₃ x ≡ (6 + (2 ∸ x)) * 5
test₃-test _ = refl

infixr 0 _⊚_

_⊚_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
f ⊚ g = λ x → f (g x)

test₃½ : Nat → Nat
test₃½ = _* 5 ⊚ 6 +_ ⊚ 2 ∸_

test₃½-test : ∀ x → test₃½ x ≡ (6 + (2 ∸ x)) * 5
test₃½-test _ = refl

test₄ : Nat → Nat → Nat
test₄ = Common.Prelude.if true then_else_

test₄-test : ∀ x y → test₄ x y ≡ x
test₄-test _ _ = refl

test₅ : Bool → Nat
test₅ = if_then 2 else 3

test₅-test : ∀ x → test₅ x ≡ (if x then 2 else 3)
test₅-test _ = refl

postulate
  foo_bar_ : (b₁ b₂ : Bool) → if b₁ then Nat else if b₂ then Bool else Nat

test₆ : (b : Bool) → if b then Bool else Nat
test₆ = foo false bar_

test₆-test : ∀ x → test₆ x ≡ (foo false bar x)
test₆-test _ = refl

test₇ : Nat → Nat
test₇ = (Common.Prelude._+ 2) ∘ (1 Common.Prelude.∸_)

test₇-test : ∀ x → test₇ x ≡ (1 Common.Prelude.∸ x) Common.Prelude.+ 2
test₇-test _ = refl

_test₈_ : Nat → Nat → Nat
_test₈_ = _*_

test₈-test : ∀ x y → (x test₈ y) ≡ x * y
test₈-test _ _ = refl

test₉ : Nat → Nat → Nat
test₉ = Common.Prelude._*_

test₉-test : ∀ x y → test₉ x y ≡ x Common.Prelude.* y
test₉-test _ _ = refl

data D : Set₂ where
  ⟨_⟩_ : Set → Set₁ → D

Test₁₀ : D → Set
Test₁₀ (⟨_⟩_ X _) = X

Test₁₁ : Set → Set
Test₁₁ ⟨_⟩ = ⟨_⟩

postulate
  ⟦_⟧ : Set → Set

Test₁₂ : Set → Set
Test₁₂ A = ⟦_⟧ A

Test₁₂-test : ∀ X → Test₁₂ X ≡ ⟦ X ⟧
Test₁₂-test _ = refl

module M where

  _! : Set₁ → Set₁
  X ! = X

Test₁₃ : Set₁
Test₁₃ = M._! Set

Test₁₄ : (x : Nat → Nat) → x ≡ suc → Set₁
Test₁₄ .(1 +_) refl = Set

_$_ : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → A → B
f $ x = f x

test₁₅ : (((⊤ → Bool) → Bool) → Nat) → Nat
test₁₅ = _$ _$ _

postulate
  -_  : Nat → Nat
  _-_ : Nat → Nat → Nat

test₁₆ : Nat → Nat
test₁₆ = (-_)

test₁₆-test : ∀ x → test₁₆ x ≡ (- x)
test₁₆-test _ = refl

test₁₇ : (f : Nat → Nat) → f ≡ suc → Set₁
test₁₇ .(1 +_) refl = Set

test₁₈ : (section : Nat) → section +_ ≡ λ x → section + x
test₁₈ section = refl
