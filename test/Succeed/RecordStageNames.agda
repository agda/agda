{-# OPTIONS --double-check -WnoRecordStageName #-}

module RecordStageNames where

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

record Foo (A : Set) : Set where
  B = A
  field b : B

-- Both the fully qualified and the stage-qualified constructor types work.
c : {A : Set} → Foo.0.B A → Foo A
c = Foo.constructor

record Hidden {A : Set} : Set where
  B = A
  field b : B

hidden : {A : Set} → Hidden.0.B {A} → Hidden {A}
hidden = Hidden.constructor

record RF : Set₁ where
  field A : Set
  private
    F : Bool → Set
    F true = A
    F false = A → A
  field value : (b : Bool) → F b

-- Private helpers are available in stages, with field values as parameters.
makeRF : (A : Set) (value : (b : Bool) → RF.1.F A b) → RF
makeRF = RF.constructor

module Stage = RF.1 Bool
_ : Stage.F false ≡ (Bool → Bool)
_ = refl

module OpenStage where
  open RF.1 Bool
  _ : F true ≡ Bool
  _ = refl

-- Opening the record does not interfere with qualified stage access.
open RF
_ : RF.1.F Bool true ≡ Bool
_ = refl

module Parameterised (T : Set) where
  record R : Set where
    field x : T
    G : Bool → Set
    G true = T
    G false = T → T
    field y : (b : Bool) → G b
  make : (x : T) (y : (b : Bool) → R.1.G x b) → R
  make = R.constructor

-- Ordinary copying exports record members, and an explicitly exported stage
-- alias, but no implicit stage aliases.
module Copy = Parameterised Bool
module Exported = RF.1 Bool

record Multiple (A : Set) : Set where
  field first second : A
  G : Bool → Set
  G true = A
  G false = A → A
  field third : (b : Bool) → G b

-- Empty stages still count; the helper takes both preceding field values.
makeMultiple : {A : Set} (x y : A) (z : (b : Bool) → Multiple.2.G A x y b) → Multiple A
makeMultiple = Multiple.constructor

record Operators : Set₁ where
  infixr 4 _⇒_
  _⇒_ : Set → Set → Set
  A ⇒ B = A → B
  field value : Set

-- Operator-part lookup must traverse stage selectors too.
_ : (Operators.0._⇒_ Bool Bool) ≡ (Bool → Bool)
_ = refl
_ : (Bool Operators.0.⇒ Bool) ≡ (Bool → Bool)
_ = refl

module Nested where
  record Outer : Set₁ where
    field A : Set
    record Inner : Set₁ where
      B = A
      field x : B
    -- Inner's stages are private to this surrounding stage.
    makeInner : Inner.0.B → Inner
    makeInner = Inner.constructor
    field value : Inner
    -- The public copy of Inner has its own private stages, inside Outer.
    makePublicInner : Inner.0.B → Inner
    makePublicInner = Inner.constructor

-- Nested private modules stay private in the final record, but the module
-- itself can be named through the stage.
record WithModule : Set₁ where
  private
    module M where
      T = Set
  field x : M.T
_ : WithModule.0.M.T ≡ Set
_ = refl
