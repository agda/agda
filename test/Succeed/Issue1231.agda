
data Nat : Set where
  zero : Nat

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

subst : ∀ {A : Set} (P : A → Set) {x y} → x ≡ y → P x → P y
subst P refl px = px

postulate
  Eq : Set → Set
  mkEq : {A : Set} (x y : A) → x ≡ y
  _==_ : {A : Set} {{_ : Eq A}} (x y : A) → x ≡ y

  A : Set
  B : A → Set
  C : ∀ x → B x → Set

case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x

id : ∀ {a} (A : Set a) → A → A
id A x = x

eqTriple : {{_ : ∀ {x} {y : B x} → Eq (C x y)}}
           (a : A) (b : B a) (c : C a b)
           (a₁ : A) (b₁ : B a₁) (c : C a₁ b₁) → Nat
eqTriple a b c a₁ b₁ c₁ =
  subst (λ a₂ → ∀ (b₂ : B a₂) (c₂ : _) → Nat) (mkEq a a₁)
        (λ b₂ c₂ → subst (λ b₃ → ∀ c₃ → Nat) (mkEq b b₂)
                           (λ c₃ → case c == c₃ of λ eq → zero) c₂)
        b₁ c₁
