-- Andreas, 2026-09-01, issue #8698.
--
-- The check for named where-modules in with-clauses that re-type
-- a module parameter (error NamedWhereModuleInRetypedContext)
-- must not fire when nothing has been re-typed.

{-# OPTIONS --safe --without-K #-}

module Issue8698 where

open import Agda.Builtin.Bool
open import Agda.Builtin.Unit

data ⊥ : Set where

neg : Bool → Bool
neg true  = false
neg false = true

F : Bool → Set
F true  = ⊥
F false = ⊤

module M (b : Bool) (p : F (neg b)) where

  get : F (neg b)
  get = p

  -- Here the with-expression does not mention b,
  -- so the type of p survives the with-abstraction.
  bar : Bool → Bool
  bar x with neg x
  ... | c = c
    module W where
    val : F (neg b)
    val = get

  -- Anonymous where-blocks are never restricted.
  foo : Bool
  foo with neg b
  ... | true  = true
  ... | false = aux
    where
    aux : Bool
    aux = false

-- W honestly gets the telescope (b : Bool) (p : F (neg b)) (x c : Bool).
test : ⊤
test = M.W.val true tt true true
