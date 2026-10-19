{-# OPTIONS --without-K --safe #-}

open import Agda.Primitive renaming (Set to Type)

-- -- Identity types

data _＝_ {𝓤} {A : Type 𝓤} (a : A) : A → Type 𝓤 where
  refl : a ＝ a

subst : ∀ {𝓤 𝓥} {A : Type 𝓤} (B : A → Type 𝓥) {a b : A} → a ＝ b → B a → B b
subst B refl pa = pa

ap : ∀ {𝓤 𝓥} {A : Type 𝓤} {B : Type 𝓥} (f : A → B) {a b : A} → a ＝ b → f a ＝ f b
ap f refl = refl

apd : ∀ {𝓤 𝓥} {A : Type 𝓤} {B : A → Type 𝓥}
        (f : (a : A) → B a) {a b : A} (p : a ＝ b) → subst B p (f a) ＝ f b
apd f refl = refl

_∙_ : ∀ {𝓤} {A : Type 𝓤} {x y z : A} → x ＝ y → y ＝ z → x ＝ z
_∙_ p refl = p

sym : ∀ {𝓤} {A : Type 𝓤} {x y : A} → x ＝ y → y ＝ x
sym refl = refl

∙-left-unit : ∀ {𝓤} {A : Type 𝓤} {x y : A} (p : x ＝ y) → (refl ∙ p) ＝ p
∙-left-unit refl = refl

∙-left-cancel
  : ∀ {𝓤} {A : Type 𝓤} {x y z : A} (a : x ＝ y) (p q : y ＝ z)
    → (a ∙ p) ＝ (a ∙ q) → p ＝ q
∙-left-cancel refl p q h = sym (∙-left-unit p) ∙ (h ∙ ∙-left-unit q)

subst-Id-right
  : ∀ {𝓤} {A : Type 𝓤} {x y : A} (p : x ＝ y) (r : x ＝ x)
    → subst (x ＝_) p r ＝ (r ∙ p)
subst-Id-right refl r = refl

-- -- Propositions

is-prop : ∀ {𝓤} → Type 𝓤 → Type 𝓤
is-prop A = (x y : A) → x ＝ y

-- If a propositional reflexive binary relation maps into the identity types
-- then they are propositions (Theorem 7.2.2, UF13)
prop-in-Id
  : ∀ {𝓤 𝓥} {A : Type 𝓤} (x : A)
    → (R : A → Type 𝓥)
    → ((y : A) → is-prop (R y))
    → R x
    → ((y : A) → R y → x ＝ y)
    → (y : A) → is-prop (x ＝ y)
prop-in-Id {A = A} x R R-is-prop ρ f .x p refl =
  ∙-left-cancel (f x ρ) p refl (loop-fixed p)
  where
    subst-f
      : {y : A} (p : x ＝ y)
      → subst (λ z → R z → x ＝ z) p (f x) (subst R p ρ)
      ＝ subst (x ＝_) p (f x ρ)
    subst-f refl = refl

    loop-fixed : (p : x ＝ x) → (f x ρ ∙ p) ＝ f x ρ
    loop-fixed p =
      sym (subst-Id-right p (f x ρ))
      ∙ ( sym (subst-f p)
        ∙ ( ap (λ h → h (subst R p ρ)) (apd f p)
          ∙ ap (f x) (R-is-prop x (subst R p ρ) ρ)))

-- -- Irrelevance

data ⊥ : Type where

record Squash {𝓤} (A : Type 𝓤) : Type 𝓤 where
  constructor lift
  field .lower : A

open Squash

is-prop-Squash : ∀ {𝓤} {A : Type 𝓤} → is-prop (Squash A)
is-prop-Squash _ _ = refl

case_of_ : ∀ {𝓤 𝓥} {A : Type 𝓤} {B : Type 𝓥} → Squash A → (.A → B) → B
case (lift x) of f = f x

no-squash-⊥ : Squash ⊥ → ⊥
no-squash-⊥ ()

-- Proof of global choice under Squash

squash-global-choice : ∀ {𝓤} → Squash ({A : Type 𝓤} → Squash A → A)
squash-global-choice .lower (lift x) = x

-- Proof of not not K

is-set : ∀ {𝓤} → Type 𝓤 → Type 𝓤
is-set A = (x y : A) → is-prop (x ＝ y)

squash-K : ∀ {𝓤} → Squash ({A : Type 𝓤} → is-set A)
squash-K =
  case squash-global-choice of
    ( λ choose →
      lift
        ( λ {A} x →
          prop-in-Id x
            (λ y → Squash (x ＝ y))
            (λ _ → is-prop-Squash)
            (lift refl)
            (λ _ → choose)))

¬¬K : ∀ {𝓤} → (({A : Type 𝓤} → is-set A) → ⊥) → ⊥
¬¬K ¬K = no-squash-⊥ (case squash-K of λ K → lift (¬K K))
