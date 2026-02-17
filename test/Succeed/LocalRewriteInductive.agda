{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

-- Based on 7.3: Inductive Types from https://hal.science/hal-05160846/document
module LocalRewriteInductive where

module Utils where
  private variable
    A B C : Set _
    x y z : A

  ap : (f : A → B) → x ≡ y → f x ≡ f y
  ap f refl = refl
open Utils

record Naturals : Set₁ where
  field
    Nat : Set
    ze  : Nat
    su  : Nat → Nat

    elim : (P : Nat → Set) → P ze → (∀ n → P n → P (su n)) → ∀ n → P n

  elim-ze≡ : Set₁
  elim-ze≡ = ∀ {P z s} → elim P z s ze ≡ z

  elim-su≡ : Set₁
  elim-su≡ = ∀ {P z s n} → elim P z s (su n) ≡ s n (elim P z s n)
open Naturals using (elim-ze≡; elim-su≡)

module UsingNaturals (𝒩 : Naturals)
                     (@rew elim-ze : elim-ze≡ 𝒩)
                     (@rew elim-su : elim-su≡ 𝒩)
                     where
  open Naturals 𝒩

  _+_ : Nat → Nat → Nat
  n + m = elim _ m (λ _ → su) n

  test₁ : su (su ze) + su ze ≡ su (su (su ze))
  test₁ = refl

  +ass : ∀ {n m l} → (n + m) + l ≡ n + (m + l)
  +ass {n = n} {m = m} {l = l}
    = elim (λ □ → (□ + m) + l ≡ □ + (m + l)) refl (λ _ → ap su) n

module Test1 where
  open import Agda.Builtin.Nat renaming (zero to ze; suc to su)

  primNaturals : Naturals
  primNaturals .Naturals.Nat  = Nat
  primNaturals .Naturals.ze   = ze
  primNaturals .Naturals.su   = su
  primNaturals .Naturals.elim P z s ze = z
  primNaturals .Naturals.elim P z s (su n)
    = s n (primNaturals .Naturals.elim P z s n)

  module N = UsingNaturals primNaturals refl refl

  test₂ : 2 N.+ 1 ≡ 3
  test₂ = refl

module W-encoding where
  open import Agda.Builtin.Nat renaming (zero to ze; suc to su)

  private variable
    A B : Set
    n m : Nat

  data Vec (A : Set) : Nat → Set where
    []   : Vec A ze
    _,-_ : A → Vec A n → Vec A (su n)

  variable
    x y   : A
    xs ys : Vec _ _
    rec   : A → Nat

  data All (P : A → Set) : Vec A n → Set where
    []   : All P []
    _,-_ : P x → All P xs → All P (x ,- xs)

  data W (A : Set) (rec : A → Nat) : Set where
    c : (x : A) → Vec (W A rec) (rec x) → W A rec

  elim : (P : W A rec → Set)
       → (∀ {x xs} → All P xs → P (c x xs))
       → ∀ x → P x
  elim' : (P : W A rec → Set)
        → (∀ {x xs} → All P xs → P (c x xs))
        → (xs : Vec (W A rec) n) → All P xs

  elim P p (c x xs) = p (elim' P p xs)

  elim' P p []        = []
  elim' P p (x ,- xs) = elim P p x ,- elim' P p xs

  open import Agda.Builtin.Bool

  natPositions : Bool → Nat
  natPositions true  = 1
  natPositions false = 0

  wNaturals : Naturals
  wNaturals .Naturals.Nat  = W Bool natPositions
  wNaturals .Naturals.ze   = c false []
  wNaturals .Naturals.su n = c true (n ,- [])
  wNaturals .Naturals.elim P z s (c false [])
    = z
  wNaturals .Naturals.elim P z s (c true  (n ,- []))
    = s n (wNaturals .Naturals.elim P z s n)

  module N = UsingNaturals wNaturals refl refl

  test₃ :   c true (c true (c false [] ,- []) ,- [])
        N.+ c true (c false [] ,- [])
        ≡   c true (c true (c true (c false [] ,- []) ,- []) ,- [])
  test₃ = refl
