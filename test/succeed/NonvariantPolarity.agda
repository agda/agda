-- Andreas, 2012-09-15
-- Positive effects of making Agda recognize constant functions.
-- Arguments to constant functions are ignored in definitional equality.
{-# OPTIONS --copatterns #-}
module NonvariantPolarity where

open import Common.Equality

data ⊥ : Set where
record ⊤ : Set where
  constructor trivial

data Bool : Set where
  true false : Bool

True : Bool → Set
True true  = ⊤
True false = ⊥

module IgnoreArg where

  -- A function ignoring its first argument
  knot : Bool → Bool → Bool
  knot x true  = false
  knot x false = true

  test : (y : Bool) → knot true y ≡ knot false y
  test y = refl

module UnusedModulePar where

  -- An unused module parameter
  module M (x : Bool) where

    not : Bool → Bool
    not true  = false
    not false = true

  open M true
  open M false renaming (not to not′)

  test : (y : Bool) → not y ≡ not′ y
  test y = refl

module Absurd where

  -- Absurd patterns do not count as matches; abort is constant in its 2nd arg.
  abort : (A : Set) → ⊥ → A
  abort A ()

  test : (x y : ⊥) → abort Bool x ≡ abort Bool y
  test x y = refl

module ProofIrrelevance where

  -- Record and absurd patterns do not count as match.
  fun : (b : Bool) → True b → Bool
  fun true  trivial = true
  fun false ()

  -- This gives us a kind of proof irrelevance.
  test : (b : Bool) → (x y : True b) → fun b x ≡ fun b y
  test b x y = refl

module CoinductiveUnit where

  record Unit : Set where
    coinductive
    constructor delay
    field force : Unit
  open Unit

  -- The identity on Unit does not match on its argument, so it is constant.
  id : Unit → Unit
  force (id x) = id (force x)

  idConst : (x y : Unit) → id x ≡ id y
  idConst x y = refl

  -- That does not imply x ≡ y (needs bisimulation).

