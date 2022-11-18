{-# OPTIONS --v assumption:20 #-}

module ScopedAssumption where

open import ReflectionWellScoped


open import Data.Bool.Base
open import Data.List.Base
open import Data.Maybe.Base as M using (Maybe; just; nothing)
open import Data.Nat.Base
open import Data.Product using (proj₂)
open import Level using (Level)
open import Data.Unit.Base
open import Function.Base
open import Relation.Nullary

private
  variable
    a b : Level
    A : Set a
    B : Set b
    m n p : ℕ

open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality

data SnocTele (A : ℕ → Set) (n : ℕ) : ℕ → Set where
  emptySnocTele : SnocTele A n n
  extSnocTele   : SnocTele A n m → A m → SnocTele A n (suc m)

_<><_ : {A : ℕ → Set} → SnocTele A m n → Tele A n p → SnocTele A m (p + n)
_<><_ {n = n} ez emptyTel = ez
_<><_ {m = m} {n} {p = suc p} ez (extTel t es)
  rewrite sym (+-suc p n) = extSnocTele ez t <>< es

toSnocTele : {A : ℕ → Set} → Tele A m n → SnocTele A m (n + m)
toSnocTele ts = emptySnocTele <>< ts

toSnocTele0 : {A : ℕ → Set} → Tele A 0 n → SnocTele A 0 n
toSnocTele0 {n = n} {A = A} tel = subst (SnocTele A 0) (+-identityʳ n) (toSnocTele tel)

searchEntry : Type m → SnocTele Type n m → Maybe (Var m)
searchEntry ty emptySnocTele = nothing
searchEntry ty (extSnocTele ez e) = let open M in do
  ty ← strengthenType (skip ones) ty
  case ty ≟Type e of λ where
    (just eq) → just zero
    nothing   → M.map suc (searchEntry ty ez)


mapTele : {A B : ℕ → Set} → (∀ {n} → A n → B n) → Tele A m n → Tele B m n
mapTele f emptyTel = emptyTel
mapTele f (extTel t ts) = extTel (f t) (mapTele f ts)

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
    let asss = mapTele (unArg ∘ proj₂) asss
    goal ← inferType hole
    mkTC $ R.debugPrint "assumption" 10
      (R.strErr "Context : "
       ∷ concatMap (λ ty → R.strErr "\n  " ∷ R.termErr ty ∷ [])
                   (unscopeTele unscopeTerm asss))
    let res = searchEntry goal (toSnocTele0 asss)
    case res of λ where
      nothing → typeError (strErr "Couldn't find an assumption of type: " ∷ termErr goal ∷ [])
      (just idx) → unify hole (var idx [])

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
