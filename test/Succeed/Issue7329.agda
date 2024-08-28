
module _ where

open import Agda.Builtin.Reflection renaming (bindTC to _>>=_)
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat hiding (_==_)
open import Agda.Builtin.List
open import Agda.Builtin.Equality

Tactic = Term → TC ⊤

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

  -- Look up the type of the first constructor of a type
  `typeOfCon : Name → Tactic
  `typeOfCon d hole = getDefinition d >>= λ where
    (data-type _ (c ∷ _)) → getType c >>= unify hole
    (record-type c _)     → getType c >>= unify hole
    _                     → typeError (strErr "bad" ∷ [])

-- Some convenience functions
data ⊥ : Set where

infix 0 _∋_
_∋_ : ∀ {a} (A : Set a) → A → A
A ∋ x = x

_≢_ : ∀ {a} {A : Set a} → A → A → Set a
x ≢ y = x ≡ y → ⊥

-- As in #7182 we make a parameterised module
module Param (A : Set) where

  record UnnamedRecord : Set where
    field
      getField : A

  record NamedRecord : Set where
    constructor namedCon
    field
      getField : A

-- but now we reexport it from another parameterised module
module Reexport (A : Set) where
  open Param A public

-- and then apply the reexporting module
module Indirect = Reexport Nat
module Direct   = Param Nat

-- The types of the parameterised records are ok.
_ = `typeOfCon Param.UnnamedRecord    ≡ ({A : Set} → A → Param.UnnamedRecord A) ∋ refl
_ = `typeOfCon Reexport.UnnamedRecord ≡ ({A : Set} → A → Reexport.UnnamedRecord A) ∋ refl

-- The type of the named record constructor is also ok,
_ = `typeOfCon Indirect.NamedRecord ≡ (Nat → Indirect.NamedRecord) ∋ refl

-- as is the one instantiated directly,
_ = `typeOfCon Direct.UnnamedRecord ≡ (Nat → Direct.UnnamedRecord) ∋ refl

-- but the type of the instantiated constructor was wrong (the parameterised type)
_ = `typeOfCon Indirect.UnnamedRecord ≡ (Nat → Indirect.UnnamedRecord) ∋ refl

-- It wasn't the constructor itself that is wrong, we do get a distinct constructor
_ = `con Indirect.UnnamedRecord ≢ `con Param.UnnamedRecord    ∋ λ ()
_ = `con Indirect.UnnamedRecord ≢ `con Reexport.UnnamedRecord ∋ λ ()
