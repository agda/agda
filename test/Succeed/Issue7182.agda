
module _ where

open import Agda.Builtin.Reflection renaming (bindTC to _>>=_)
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat hiding (_==_)
open import Agda.Builtin.List
open import Agda.Builtin.Equality

Tactic = Term → TC ⊤

variable A B C : Set

pattern vArg x = arg (arg-info visible (modality relevant quantity-ω)) x
pattern _`∷_ x xs = con (quote _∷_) (vArg x ∷ vArg xs ∷ [])

`nameList : List (Arg Name) → Term
`nameList [] = con (quote []) []
`nameList (arg _ x ∷ xs) = lit (name x) `∷ `nameList xs

macro
  -- Get the (first) constructor of a data or record type
  `con : Name → Tactic
  `con x hole = getDefinition x >>= λ where
    (data-type _ (c ∷ _)) → unify hole (lit (name c))
    (record-type c _)     → unify hole (lit (name c))
    _                     → typeError (strErr "bad" ∷ [])

  `fields : Name → Tactic
  `fields x hole = getDefinition x >>= λ where
    (record-type _ fs)    → unify hole (`nameList fs)
    _                     → typeError (strErr "bad" ∷ [])

  -- Look up the name of a name
  `typeOf : Name → Tactic
  `typeOf x hole = getType x >>= unify hole

-- Some convenience functions
data ⊥ : Set where

infix 0 _∋_
_∋_ : ∀ {a} (A : Set a) → A → A
A ∋ x = x

_≢_ : ∀ {a} {A : Set a} → A → A → Set a
x ≢ y = x ≡ y → ⊥

-- If we put a data type and a record type in a parameterised module
module Param (A : Set) where

  data Data : Set where
    mkData : A → Data

  record Record : Set where
    constructor mkRecord
    field getField : A

-- and then apply the module to some argument
open Param Nat

-- getDefinition Data behaves as expected, returning a definition with a constructor
-- Data.mkData : Nat → Data
_ = `con Data           ≡ quote Data.mkData ∋ refl
_ = `typeOf Data.mkData ≡ (Nat → Data)      ∋ refl

-- Although it's interesting that we get Data.mkData and not mkData (and that these are
-- not the same).
_ = quote Data.mkData ≢ quote mkData ∋ λ ()

-- But, we don't get `Param.mkData : {A : Set} → A → Param.Data A`
_ = `con Data            ≢ quote Param.mkData             ∋ λ ()
_ = `typeOf Param.mkData ≡ ({A : Set} → A → Param.Data A) ∋ refl

-- The same should be true for the record type
_ = `con Record            ≢ quote Param.mkRecord             ∋ λ ()
_ = `con Record            ≡ quote mkRecord                   ∋ refl
_ = `typeOf Param.mkRecord ≡ ({A : Set} → A → Param.Record A) ∋ refl
_ = `typeOf mkRecord       ≡ (Nat → Record) ∋ refl

-- The field should also point to the instantiated field
_ = `fields Record ≡ quote Record.getField ∷ []                      ∋ refl
_ = `typeOf Record.getField       ≡ (Record → Nat)                   ∋ refl
_ = `typeOf Param.Record.getField ≡ ({A : Set} → Param.Record A → A) ∋ refl
