{-# OPTIONS -v intros:40 #-}

module ScopedIntroList where

open import Data.Maybe.Base using (Maybe; just)
open import Data.Bool.Base
open import Level using (Lift; Setω)
open import Data.Nat.Base
open import Data.List.Base
open import Function.Base
open import Data.Unit.Base
open import ReflectionWellScopedList
open import Agda.Builtin.String
import Agda.Builtin.Reflection as R
open import Data.Product
open import Data.Empty

private
  variable
    n : SnocList String
    A B : Set
  _>>=_ = bindTC
  _>>_ : TC n A → TC n B → TC n B
  m >> n = bindTC m (λ _ → n)

------------------------------------------------------------------------
-- Errors

impossible : List (ErrorPart n) → TC n A
impossible fmt = typeError (strErr "IMPOSSIBLE" ∷ fmt)

fromJust : Maybe A → TC n A
fromJust (just a) = returnTC a
fromJust _ = impossible []

confused : ℕ → Type n → TC n (Term n)
confused lvl ty
  = do debugPrint "intros" lvl
         $ strErr "I do not know how to proceed with type: " ∷ termErr ty ∷ []
       returnTC unknown

------------------------------------------------------------------------
-- Emptiness check

{-# TERMINATING #-}
isEmpty : Type n → TC n Bool
anyEmpty : List (Arg Name) → List (Arg (Term n)) → TC n Bool

anyEmpty [] _ = returnTC false
anyEmpty (arg _ c ∷ ns) ts = do
  ty ← getType c
  pi a (abs x ty) ← fromJust (specialise ty ts)
    where _ → impossible []
  b ← extendContext x a $ do
    debugPrint "intros" 40 (nameErr c ∷ strErr "ts : " ∷ termErr ty ∷ [])
    isEmpty ty
  if b then returnTC true else anyEmpty ns ts

isEmpty (def f args) = do
  d ← getDefinition f
  case d of λ where
    (data-type pars []) → returnTC true
    (record-type c flds) → anyEmpty flds args
    _ → returnTC false
isEmpty t = do
  debugPrint "intros" 40 (termErr t ∷ strErr " is not a def" ∷ [])
  returnTC false

------------------------------------------------------------------------
-- intros

{-# TERMINATING #-}
introsₙ : ℕ → ℕ → Term n → TC n (Term n)

apply : ℕ → ℕ → (List (Arg (Term n)) → Term n) → Type n → TC n (Term n)
apply fuel lvl acc (pi (arg i a) (abs s b)) = do
  debugPrint "intros" 40 (strErr "Searching for a value of type " ∷ termErr a ∷ [])
  x ← introsₙ fuel lvl a
  debugPrint "intros" 40 (strErr "Found " ∷ termErr x ∷ [])
  b ← fromJust (subTerm [ x /0] b)
  debugPrint "intros" 40 (strErr "Now searching for something of type " ∷ termErr b ∷ [])
  b ← reduce b
  apply fuel lvl (acc ∘′ (arg i x ∷_)) b
apply fuel lvl acc (def _ _) = returnTC (acc [])
apply fuel lvl acc ty = impossible (termErr ty ∷ [])

refine : ℕ → ℕ → Name → List (Arg (Term n)) → TC n (Term n)
refine 0 lvl n args = do
  debugPrint "intros" lvl
         $ strErr "Giving up on: " ∷ nameErr n ∷ []
  returnTC unknown
refine (suc fuel) lvl n args = do
  ty ← getType n
  ty ← fromJust (specialise ty args)
  debugPrint "intros" 60 (nameErr n ∷ strErr ": " ∷ termErr ty ∷ [])
  apply fuel (suc lvl) (con n) ty

introsₙ fuel lvl (pi a@(arg info@(arg-info v m) dom) (abs x b)) = do
  dom ← reduce dom
  empty ← isEmpty dom
  debugPrint "intros" 40 (strErr "The type " ∷ termErr dom ∷ strErr (if empty then " is " else " is not ") ∷ strErr "empty" ∷ [])
  if empty then returnTC (pat-lam (absurd-clause (extTel x a emptyTel) (arg info (absurd here) ∷ []) ∷ []) []) else do
    debugPrint "intros" 40 (strErr "Binding " ∷ strErr x ∷ strErr " : " ∷ termErr dom ∷ [])
    body ← extendContext x a (introsₙ fuel lvl b)
    returnTC (lam v (abs x body))
introsₙ fuel lvl t@(def f args) = do
  d ← getDefinition f
  case d of λ where
    (data-type pars (c ∷ [])) → refine fuel lvl c (take pars args)
    (data-type pars cs) → confused lvl t
    (record-type c fs) → refine fuel lvl c args
    _ → confused lvl t
introsₙ fuel = confused

macro

  intros : R.Term → R.TC ⊤
  intros = mkMacro λ goal → do
    ty ← inferType goal
    tm ← introsₙ 1 10 ty
    debugPrint "intros" 20 (strErr "I came up with: " ∷ termErr tm ∷ [])
    unify goal tm

data Tree (A : Set) : Set where
  node : (f : (x : A) → Tree A) → Tree A

data Empty : Set where
  oops : Empty → Empty

example : (m n p : ℕ) → Tree ⊤
example = {!!}

example₀ : (l : Level.Level) → (A : Set l) → (x : A) → Σ A (λ _ → A) -- does not work due to erased parameters
example₀ = {!!}

record Triple : Set where
  field
   fst : ⊤
   snd : ℕ → ⊤
   thd : ⊥ → ⊤

example₁′ : ⊤ × (ℕ → ⊤) × (⊥ → ⊤)
example₁′ = {!!}

example₁ : Triple
example₁ = {!!}

example₃ : Tree ⊥
example₃ = {!!}

example₄ : ⊥ → ℕ
example₄ = {!!}
