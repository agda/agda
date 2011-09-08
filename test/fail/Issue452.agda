module Issue452 where

data Bool : Set where
  true false : Bool

data ⊥ : Set where

record ⊤ : Set where
  constructor tt

abstract

  id : Bool → Bool
  id b = b

If_then_else_ : Bool → Set → Set → Set
If true  then t else f = t
If false then t else f = f

data D : (b : Bool) → If b then ⊤ else ⊥ → Set where
  d : D (id true) _  -- this meta variable (type If (id true) ...) is unsolvable

foo : D true tt → ⊥
foo ()
-- An internal error has occurred. Please report this as a bug.
-- Location of the error: src/full/Agda/TypeChecking/Rules/LHS/Unify.hs:402

{- Trying to unify

  D true tt = D (id true) _

true = id true is postponed, but then tt is handled of type 

  If (id true)...

which is not a data or record type, causing the panic

Solution: do not postpone but fail, since in D : (b : Bool) -> X 

  X depends on b

-}
