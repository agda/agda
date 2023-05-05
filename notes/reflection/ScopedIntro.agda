{-# OPTIONS -v intros:20 #-}

module ScopedIntro where

open import Level using (Lift)
open import Data.Nat.Base
open import Data.List.Base
open import Function.Base
open import Data.Unit.Base
open import ReflectionWellScoped
import Agda.Builtin.Reflection as R

private
  variable
    n : ℕ
    A B : Set
  _>>=_ = bindTC
  _>>_ : TC n A → TC n B → TC n B
  m >> n = bindTC m (λ _ → n)

{-# TERMINATING #-}
introsₙ : ℕ → ℕ → Term n → TC n (Term n)

apply : ℕ → ℕ → (List (Arg (Term n)) → Term n) → Type n → TC n (Term n)
apply fuel lvl acc (pi (arg i a) (abs s b)) = do
  x ← introsₙ fuel lvl a
  b ← normalise (subTerm [ x /0] b)
  apply fuel lvl (acc ∘′ (arg i x ∷_)) b
apply fuel lvl acc (def _ _) = returnTC (acc [])
apply fuel lvl acc ty = typeError (strErr "IMPOSSIBLE: " ∷ termErr ty ∷ [])

refine : ℕ → ℕ → Name → TC n (Term n)
refine 0 lvl n = do
  debugPrint "intros" lvl
         $ strErr "Giving up on: " ∷ nameErr n ∷ []
  returnTC unknown
refine (suc fuel) lvl n = do
  ty ← getType n
  debugPrint "intros" 30 (nameErr n ∷ strErr ": " ∷ termErr ty ∷ [])
  apply fuel (suc lvl) (con n) ty

confused : ℕ → Type n → TC n (Term n)
confused lvl ty
  = do debugPrint "intros" lvl
         $ strErr "I do not know how to proceed with type: " ∷ termErr ty ∷ []
       returnTC unknown

introsₙ fuel lvl (pi a@(arg (arg-info v m) _) (abs x b)) = do
  body ← extendContext x a (introsₙ fuel lvl b)
  returnTC (lam v (abs x body))
introsₙ fuel lvl t@(def f args) = do
  d ← getDefinition f
  case d of λ where
    (data-type pars (c ∷ [])) → refine fuel lvl c
    (data-type pars cs) → confused lvl t
    (record-type c fs) → refine fuel lvl c
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
example = {!!} -- intros
