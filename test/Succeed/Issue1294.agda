-- Andreas, 2014-10-08, issue reported by Andrea Vezzosi

{-# OPTIONS --copatterns #-}

import Common.Level
open import Common.Product

postulate Nat : Set

record Cxt : Set₁ where
  constructor Con  -- essential
  field
    CSet : Set
    CRel : (e0 e1 : CSet) → Set


record Type (Γ : Cxt) : Set₁ where
  open Cxt
  field
    TSet : (e : CSet Γ) → Set
    TRel : (e : CSet Γ) →
           ([e] : CRel Γ e e) →
           (t : TSet e) → Set

open Type

module Works where

  T : (Γ : Cxt) → (a : Type Γ) → Type Γ
  TSet (T Γ a) γ             = Nat × TSet a γ
  TRel (T Γ a) γ [e] (n , b) = TRel a γ [e] b

module Works2 where

  T : (Γ : Cxt) → (a : Type Γ) → Type Γ
  TSet (T Γ a) γ                     = Nat × TSet a γ
  TRel (T (Con S R) a) γ [e] (n , b) = TRel a γ [e] b

module Fails2 where

  T : (Γ : Cxt) → (a : Type Γ) → Type Γ
  TSet (T (Con S R) a) γ     = Nat × TSet a γ
  TRel (T Γ a) γ [e] (n , b) = TRel a γ [e] b

module Fails where

  T : (Γ : Cxt) → (a : Type Γ) → Type Γ
  TSet (T (Con S R) a) γ             = Nat × TSet a γ
  TRel (T (Con S R) a) γ [e] (n , b) = TRel a γ [e] b

-- All version should work!
