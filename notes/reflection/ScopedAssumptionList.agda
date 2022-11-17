{-# OPTIONS --v assumption:20 #-}

module ScopedAssumptionList where

open import ReflectionWellScopedList


open import Data.Bool.Base
open import Data.List.Base as List
open import Data.Maybe.Base as M using (Maybe; just; nothing)
open import Data.Nat.Base
open import Data.String.Base hiding (_++_)
open import Agda.Builtin.Sigma
open import Level using (Level)
open import Data.Unit.Base
open import Function.Base
open import Relation.Nullary

private
  variable
    a b : Level
    A : Set a
    B : Set b
    m n p : SnocList String

open import Data.List.Properties
open import Relation.Binary.PropositionalEquality



searchEntry : Type m → SnocTele Type n m → Maybe (Var m)
searchEntry ty emptySnocTele = nothing
searchEntry ty (extSnocTele ez s e) = let open M in do
  ty ← strengthenType (skip ones) ty
  case ty ≟Type e of λ where
    (just eq) → just here
    nothing   → M.map there (searchEntry ty ez)

mapSnocTele : {A B : SnocList String → Set} → (∀ {n} → A n → B n) → SnocTele A n m → SnocTele B n m
mapSnocTele f emptySnocTele = emptySnocTele
mapSnocTele f (extSnocTele ts s t) = extSnocTele (mapSnocTele f ts) s (f t)

import Agda.Builtin.Reflection as R

unArg : Arg A → A
unArg (arg _ a) = a

macro
  assumption : R.Term → R.TC ⊤
  assumption = mkMacro $ λ hole →
    let _>>=_ = bindTC; _>>_ : TC n ⊤ → TC n B → TC n B; _>>_ = λ m n → bindTC m (λ _ → n) in do
    debugPrint "assumption" 20 (strErr "Getting the context" ∷ [])
    asss ← getContext
    debugPrint "assumption" 20 (strErr "Got the context" ∷ [])
    let asss = mapSnocTele unArg asss
    goal ← inferType hole
    {-mkTC $ R.debugPrint "assumption" 10
      (R.strErr "Context : "
       ∷ concatMap (λ (x , ty) → R.strErr "\n  "  ∷ R.strErr x ∷ R.strErr " : " ∷ R.termErr ty ∷ [])
                   (unscopeSnocTele unscopeTerm asss)) -}
    let res = searchEntry goal asss
    case res of λ where
      nothing → typeError (strErr "Couldn't find an assumption of type: " ∷ termErr goal ∷ [])
      (just idx) → unify hole (var idx [])

ex : (a : Level) → (A : Set a) → A → A
ex a A x = assumption



test₀ : A → B → B
test₀ x y = assumption


test₁ : A → B → A
test₁ x y = assumption

test₂ : A → B → B → A
test₂ x y z = assumption

test₃ : List (A → B) → A → B → B → List (A → B)
test₃ x y z a = assumption

test₄ : (A → List B) → A → B → List B → A → List B
test₄ x y z a = assumption

-- -}
-- -}
