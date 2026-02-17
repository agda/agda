{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Nat renaming (zero to ze; suc to su) hiding (_-_)

-- Based on 7.4: Quotients from https://hal.science/hal-05160846/document
module LocalRewriteQuotient where

module Utils where
  infixr 5 _∙_

  private variable
    A B C : Set _
    x y z : A

  sym : x ≡ y → y ≡ x
  sym refl = refl

  _∙_ : x ≡ y → y ≡ z → x ≡ z
  refl ∙ q = q

  ap : (f : A → B) → x ≡ y → f x ≡ f y
  ap f refl = refl
open Utils

variable
  A B : Set
  _≈_ : A → A → Set

record Quotients : Set₁ where
  field
    Quot  : (A : Set) → (A → A → Set) → Set
    mk    : (_≈_ : A → A → Set) → A → Quot A _≈_
    lift  : (f : A → B) → (∀ {x y} → x ≈ y → f x ≡ f y) → Quot A _≈_ → B
    sound : ∀ {x y : A} → x ≈ y → mk _≈_ x ≡ mk _≈_ y

  -- The β-law for quotients we want to make strict
  lift-mk≡ : Set₁
  lift-mk≡ = ∀ {A _≈_ B} {f : A → B} {p : ∀ {x y} → x ≈ y → f x ≡ f y} {x}
           → lift f p (mk _≈_ x) ≡ f x

open Quotients using (lift-mk≡)

module UsingQuotients (𝒬 : Quotients)
                      (@rew lift-mk : lift-mk≡ 𝒬) where
  open Quotients 𝒬

  record PreInt : Set where
    constructor _-_
    field
      pos : Nat
      neg : Nat

  _≈Int_ : PreInt → PreInt → Set
  (n₁ - k₁) ≈Int (n₂ - k₂) = n₁ + k₂ ≡ n₂ + k₁

  Int = Quot PreInt _≈Int_

  +ze : ∀ {n} → n + ze ≡ n
  +ze {n = ze}   = refl
  +ze {n = su n} = ap su +ze

  +su : ∀ {n m} → n + su m ≡ su (n + m)
  +su {n = ze}   = refl
  +su {n = su n} = ap su +su

  +comm : ∀ {n m} → n + m ≡ m + n
  +comm {m = ze}   = +ze
  +comm {m = su m} = +su ∙ ap su (+comm {m = m})

  preNegate : PreInt → PreInt
  preNegate (n - k) = k - n

  preNegate≈ : ∀ {x y} → x ≈Int y → preNegate x ≈Int preNegate y
  preNegate≈ {x = n₁ - k₁} {y = n₂ - k₂} p
    = +comm {n = k₁} ∙ sym p ∙ +comm {n = n₁}

  negate : Int → Int
  negate = lift (λ x' → mk _≈Int_ (preNegate x'))
                (λ {x₁ x₂} p → sound (preNegate≈ {x = x₁} {y = x₂} p))

  test₁ : ∀ {n k} → negate (mk _ (n - k)) ≡ mk _ (k - n)
  test₁ = refl

open Quotients

fakeQuotients : Quotients
fakeQuotients .Quot  A _≈_ = A
fakeQuotients .mk    _≈_ x = x
fakeQuotients .lift  f p x = f x
fakeQuotients .sound       = cheat
  where postulate cheat : _

open UsingQuotients fakeQuotients refl

test₂ : ∀ {n k} → negate (n - k) ≡ k - n
test₂ = refl

-- If we wanted to be really fancy, we could enable --cubical and open
-- UsingQuotients with a quotient HIT...
