-- Andreas, 2026-09-01, issue #8698, found and MWE by Claude, reported by bdrisc-ant.
--
-- With-abstraction can change the type of a module parameter
-- (namely of a parameter that is not needed to type the with-expressions
-- but whose type mentions them).
-- A named where-module in such a with-clause would get a telescope
-- that lies about the module parameters, giving us a proof of absurdity.

{-# OPTIONS --safe --without-K #-}

module Issue8698 where

data ⊥ : Set where

data ⊤ : Set where
  tt : ⊤

data Bool : Set where
  true  : Bool
  false : Bool

neg : Bool → Bool
neg true  = false
neg false = true

F : Bool → Set
F true  = ⊥
F false = ⊤

module M (b : Bool) (p : F (neg b)) where

  get : F (neg b)
  get = p

  -- The with-abstraction gives p the type F w,
  -- so in the following clause p : F false rather than F (neg b).
  foo : Bool
  foo with neg b
  ... | true  = true
  ... | false = false
    module W where
    val : F (neg b)   -- elaborated via the ill-typed application  get b p
    val = get

-- Without the check, M.W would get the telescope (b : Bool) (p : F false),
-- so the following would be a proof of ⊥:

boom : ⊥
boom = M.W.val false tt
