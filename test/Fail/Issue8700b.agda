{-# OPTIONS --safe --without-K #-}

-- Issue found by Claude and reported by bdrisc-ant on Github

-- Same mechanism, observed without any where module: the result type of
-- f's own third clause is computed (via T) by reducing f while only its
-- first two clauses are in the signature.

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

data ⊥ : Set where

T : Bool → Bool → Set
f : (x y : Bool) → T x y

T x     true  = Bool
T true  false = Bool
T false false = f (f true false) true ≡ true

f true  true  = false
f x     true  = true
f false false = refl      -- checked at  T false false  with only clauses 1-2 of f known:
                          -- f (f true false) true  reduces to  true  there
f true  false = true      -- now  f (f true false) true = f true true = false

discr : false ≡ true → ⊥
discr ()

boom : ⊥
boom = discr (f false false)
