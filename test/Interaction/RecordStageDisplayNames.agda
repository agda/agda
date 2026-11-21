{-# OPTIONS --double-check #-}

module RecordStageDisplayNames where

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Reflection using (primShowQName)
open import Agda.Builtin.String

record RF : Set₁ where
  field A : Set

  F : Bool → Set
  F true  = A
  F false = A → A

  canonicalName : String
  canonicalName = primShowQName (quote F)

  field value : (b : Bool) → F b

rf : RF
rf = record { A = Bool ; value = λ { true → true ; false → λ x → x } }

-- Diagnostic names must not change reflection's canonical names.
_ : RF.canonicalName rf ≡ "RecordStageDisplayNames.record-stage.record-stage.F"
_ = refl

-- Use an alias to the constructor when testing a binder that shadows RF.
makeRF = RF.constructor

record Initial (A : Set) : Set where
  F : Bool → Set
  F true  = A
  F false = A → A
  field value : (b : Bool) → F b

record Several : Set₁ where
  field A : Set
  F G : Bool → Set
  F true  = A
  F false = A → A
  G true  = A
  G false = Bool → A
  field
    first  : (b : Bool) → F b
    second : (b : Bool) → G b
  -- The empty helper stage before second still counts as stage 2.
  H : Bool → Set
  H true  = A
  H false = A → Bool
  field third : (b : Bool) → H b

record Submodules : Set₁ where
  field A : Set
  module M where
    F : Bool → Set
    F true  = A
    F false = A → A
  -- A user-written module with the implementation's name is not a stage.
  module record-stage where
    F : Bool → Set
    F true  = A
    F false = Bool → A
  field
    first  : (b : Bool) → M.F b
    second : (b : Bool) → record-stage.F b

record Outer : Set₁ where
  field A : Set
  record Inner : Set where
    F : Bool → Set
    F true  = A
    F false = A → A
    field value : (b : Bool) → F b
  field inner : Inner

module Copy = RF
