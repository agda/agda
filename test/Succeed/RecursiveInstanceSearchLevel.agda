{-# OPTIONS --overlapping-instances #-}

module Succeed.RecursiveInstanceSearchLevel where

open import Common.Prelude
open import Common.Product
open import Common.Equality

-- Definition of truncation levels. We wrap the definition into a datatype in
-- order to be able to use instance search.
data has-level (n : Nat) (A : Set) : Set
has-level' : (n : Nat) (A : Set) → Set

data has-level n A where
  c : has-level' n A → has-level n A

has-level' zero A = Σ A (λ a → (b : A) → a ≡ b)
has-level' (suc n) A = (a b : A) → has-level n (a ≡ b)

-- This one should not be declared as eligible by instance search or else we
-- will get unsolvable loops
postulate
  higher-level : {n : Nat} {A : Set} {{_ : has-level n A}} → has-level (suc n) A

postulate
  Trunc : Nat → Set → Set

instance
  =-level : {n : Nat} {A : Set} {{_ : has-level (suc n) A}} {a b : A} → has-level n (a ≡ b)
  =-level {{c f}} = f _ _

  postulate
    =-level-same : {n : Nat} {A : Set} {{_ : has-level n A}} {a b : A} → has-level n (a ≡ b)

  postulate
    Nat-level : has-level 2 Nat
    Π-level : {n : Nat} {A : Set} {B : A → Set} {{_ : {a : A} → has-level n (B a)}} → has-level n ((a : A) → B a)
    Πimp-level : {n : Nat} {A : Set} {B : A → Set} {{_ : {a : A} → has-level n (B a)}} → has-level n ({a : A} → B a)
    Σ-level : {n : Nat} {A : Set} {B : A → Set} {{_ : has-level n A}} {{_ : {a : A} → has-level n (B a)}} → has-level n (Σ A B)
    Trunc-level : {n : Nat} {A : Set} → has-level n (Trunc n A)

-- Used to check, using instance search, if some type has a given level
postulate
  check-level : (n : Nat) (A : Set) {{_ : has-level n A}} → Set

test₁ : (A : Set) → Set
test₁ A = check-level 1 ((a b : Trunc 2 A) → (a , (b , 3)) ≡ (b , (a , 4)))

test₂ : (A : Set) → Set
test₂ A = check-level 2 ((a b : Trunc 2 A) → (a , (b , 3)) ≡ (b , (a , 4)))

-- -- To be fixed
-- test₃ : {n : Nat} {A : Set} {B : A → Set} {_ : {a : A} → has-level n (B a)} → Nat → has-level n ((a : A) → B a)
-- test₃ r = Π-level ⟨⟩
