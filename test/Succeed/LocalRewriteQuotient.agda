{-# OPTIONS --local-rewriting --cubical #-}

open import Agda.Builtin.Equality renaming (_≡_ to _≡ᴵ_; refl to reflᴵ)
open import Agda.Builtin.Cubical.Path
open import Agda.Primitive.Cubical
open import Agda.Builtin.Nat renaming (zero to ze; suc to su) hiding (_-_)

-- Based on 7.4: Quotients from https://hal.science/hal-05160846/document
module LocalRewriteQuotient where

{-# BUILTIN REWRITE _≡ᴵ_ #-}

module Utils where
  infixr 5 _∙_

  private variable
    A B C : Set _
    x y z : A

  refl : x ≡ x
  refl {x = x} i = x

  sym : x ≡ y → y ≡ x
  sym p i = p (primINeg i)

  _∙_ : x ≡ y → y ≡ z → x ≡ z
  _∙_ {z = z} p q i
    = primHComp (λ where j (i = i0) → p (primINeg j)
                         j (i = i1) → z)
                (q i)

  ap : (f : A → B) → x ≡ y → f x ≡ f y
  ap f p i = f (p i)
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
           → lift f p (mk _≈_ x) ≡ᴵ f x

open Quotients using (lift-mk≡)

-- We define this outside of 'UsingQuotients' because of an incompatibility
-- between '--cubical' and datatypes with '@rewrite' arguments in their telescope.
-- Specifically, what should the generated type for 'transp' be?
record PreInt : Set where
  constructor _-_
  field
    pos : Nat
    neg : Nat

module UsingQuotients (𝒬 : Quotients)
                      (@rewrite lift-mk : lift-mk≡ 𝒬) where
  open Quotients 𝒬

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

module F = UsingQuotients fakeQuotients reflᴵ

test₂ : ∀ {n k} → F.negate (n - k) ≡ k - n
test₂ = refl

-- In Cubical Agda, we don't *have* to fake quotients. We can also implement
-- them with HITs.

-- Non-truncated quotient ("type quotient")
data QuotHIT (A : Set) (_≈_ : A → A → Set) : Set where
  mkHIT    : A → QuotHIT A _≈_
  soundHIT : ∀ {x y} → x ≈ y → mkHIT x ≡ mkHIT y

hitQuotients : Quotients
hitQuotients .Quot   = QuotHIT
hitQuotients .mk _≈_ = mkHIT
hitQuotients .lift  f p (mkHIT x)      = f x
hitQuotients .lift  f p (soundHIT q i) = p q i
hitQuotients .sound = soundHIT

module H = UsingQuotients hitQuotients reflᴵ

test₃ : ∀ {n k} → H.negate (mkHIT (n - k)) ≡ mkHIT (k - n)
test₃ = refl
