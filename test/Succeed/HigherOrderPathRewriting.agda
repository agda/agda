{-# OPTIONS --rewriting --cubical #-}

open import Common.Prelude
open import Common.Path

{-# BUILTIN REWRITE _≡_ #-}

postulate is-refl : ∀ {A : Set} {x : A} → (x ≡ x) → Bool
postulate is-refl-true : ∀ {A}{x} → is-refl {A} {x} refl ≡ true

{-# REWRITE is-refl-true #-}

test₁ : ∀ {x} → is-refl {Nat} {x} refl ≡ true
test₁ = refl

test₂ : is-refl {Nat} (λ _ → 42) ≡ true
test₂ = refl

postulate
    Cl : Set


module M (A B C : Set)(f : C -> A)(g : C -> B) where
  data PO : Set where
    inl : A → PO
    inr : B → PO
    push : (c : C) → inl (f c) ≡ inr (g c)

  -- elimination under clocks
  module E (D : (Cl → PO) → Set)
           (l : (x : Cl → A) → D (\ k → inl (x k)))
           (r : (x : Cl → B) → D (\ k → inr (x k)))
           (p : (x : Cl → C) → PathP (\ i → D (\ k → push (x k) i)) (l \ k → (f (x k))) (r \ k → (g (x k))))
     where

    postulate
      elim : (h : Cl → PO) → D h
      beta1 : (x : Cl → A) → elim (\ k → inl (x k)) ≡ l x
      beta2 : (x : Cl → B) → elim (\ k → inr (x k)) ≡ r x

    {-# REWRITE beta1 beta2 #-}

    _ : {x : Cl → A} → elim (\ k → inl (x k)) ≡ l x
    _ = refl
    _ : {x : Cl → B} → elim (\ k → inr (x k)) ≡ r x
    _ = refl


    postulate
      beta3 : (x : Cl → C)(i : I) → elim (\ k → push (x k) i) ≡ p x i

    {-# REWRITE beta3 #-}

    _ : {x : Cl → C}{i : I} → elim (\ k → push (x k) i) ≡ p x i
    _ = refl


-- Testing outside the module too

open M
open E

variable
  A B C : Set
  f : C → A
  g : C → B

_ : {x : Cl → A} →
    elim A B C f g (\ h → (k : Cl) → h k ≡ h k) (\ x k → refl) (\ _ _ → refl)
      (\ c i k → refl) (\ k → inl (x k)) ≡ \ k → refl
_ = refl

_ : {c : Cl → C}{i : I} →
    elim A B C f g (\ h → (k : Cl) → h k ≡ h k) (\ x k → refl) (\ _ _ → refl)
      (\ c i k → refl) (\ k → push (c k) i) ≡ \ k → refl
_ = refl
