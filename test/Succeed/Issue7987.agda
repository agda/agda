-- Andreas, 2025-07-10, issue #7987.
-- Allow erased record matches in let, and in general modalities.

{-# OPTIONS --erasure #-}
{-# OPTIONS --polarity #-}
{-# OPTIONS --cohesion #-}
{-# OPTIONS --flat-split #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma

module _ where

-- Erasure

module _ (@0 n : Nat) (let @0 m = suc n) where

  @0 k : Nat
  k = m

split : {A B C : Set} (@0 p : Σ A λ _ → B) (k : @0 A → @0 B → C) → C
split p k = let @0 (x , y) = p in k x y

split1 : {A B C : Set} (@0 p : Σ A λ _ → B) (k : @0 A → @0 B → C) → C
split1 p k = let @0 (x , y) = q in k x y
  where
  @0 q = p

-- Polarity

_ = let @-  R = Set in
    let @++ S = Set in R → S

let-spos : {A : Set₁} (@++ x : A) → A
let-spos x =
  let @++ y = x
  in  x

-- Cohesion

let-flat : {@♭ A : Set₁} (@♭ x : A) (f : @♭ A → A) → A
let-flat x f =
  let @♭ y = x
  in  f y

split-flat : {@♭ A B C : Set} (@♭ p : Σ A λ _ → B) (k : @♭ A → @♭ B → C) → C
split-flat p k = let @♭ (x , y) = p in k x y
  -- needs option --flat-split

let-flat1 : {@♭ A : Set₁} (@♭ x : A) (f : @♭ A → A) → A
let-flat1 {A} x f =
  let @♭ y : A
      y = x
  in  f y
