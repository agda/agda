
module Common.TC where

open import Common.Reflection
open import Common.Prelude

postulate
  TC         : ∀ {a} → Set a → Set a
  returnTC   : ∀ {a} {A : Set a} → A → TC A
  bindTC     : ∀ {a b} {A : Set a} {B : Set b} → TC A → (A → TC B) → TC B
  unify      : Term → Term → TC ⊤
  newMeta    : Type → TC Term
  typeError  : ∀ {a} {A : Set a} → String → TC A
  inferType  : Term → TC Type
  checkType  : Term → Type → TC Term
  normalise  : Term → TC Term
  catchTC    : ∀ {a} {A : Set a} → TC A → TC A → TC A
  getContext : TC (List (Arg Type))
  extendContext : ∀ {a} {A : Set a} → Arg Type → TC A → TC A
  inContext     : ∀ {a} {A : Set a} → List (Arg Type) → TC A → TC A

{-# BUILTIN AGDATCM           TC         #-}
{-# BUILTIN AGDATCMRETURN     returnTC   #-}
{-# BUILTIN AGDATCMBIND       bindTC     #-}
{-# BUILTIN AGDATCMUNIFY      unify      #-}
{-# BUILTIN AGDATCMNEWMETA    newMeta    #-}
{-# BUILTIN AGDATCMTYPEERROR  typeError  #-}
{-# BUILTIN AGDATCMINFERTYPE  inferType  #-}
{-# BUILTIN AGDATCMCHECKTYPE  checkType  #-}
{-# BUILTIN AGDATCMNORMALISE  normalise  #-}
{-# BUILTIN AGDATCMCATCHERROR catchTC    #-}
{-# BUILTIN AGDATCMGETCONTEXT getContext #-}
{-# BUILTIN AGDATCMEXTENDCONTEXT extendContext #-}
{-# BUILTIN AGDATCMINCONTEXT inContext #-}

Tactic = Term → TC ⊤

give : Term → Tactic
give v = λ hole → unify hole v
