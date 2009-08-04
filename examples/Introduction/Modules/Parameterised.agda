
-- This module introduces parameterised modules.

module Introduction.Modules.Parameterised where

-- First some familiar datatypes.

data Bool : Set where
  false : Bool
  true  : Bool

data List (A : Set) : Set where
  nil  : List A
  _::_ : A -> List A -> List A

infixr 15 _::_    -- see 'Introduction.Operators' for information on infix
                  -- declarations

-- Agda supports parameterised modules. A parameterised module is declared by
-- giving the parameters after the module name.

module Sorting {A : Set}(_<_ : A -> A -> Bool) where

  insert : A -> List A -> List A
  insert x  nil      = x :: nil
  insert x (y :: ys) = ins (x < y)
    where
      ins : Bool -> List A      -- local functions can do pattern matching and
      ins true  = x :: y :: ys  -- be recursive
      ins false = y :: insert x ys

  sort : List A -> List A
  sort  nil      = nil
  sort (x :: xs) = insert x (sort xs)

-- Before a parameterised module can be used it has to be instantiated. So, we
-- need something to instantiate it with.

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

_<_ : Nat -> Nat -> Bool
zero  < zero  = false
zero  < suc _ = true
suc _ < zero  = false
suc n < suc m = n < m

-- To instantiate a module you define a new module in terms of the
-- parameterised module. Module instantiation also supports the using, hiding
-- and renaming modifiers.
module SortNat = Sorting _<_

sort' : {A : Set}(_<_ : A -> A -> Bool) -> List A -> List A
sort' less = Sort'.sort
  where
    module Sort' = Sorting less

-- Now the instantiated module can be opened and we can use the sorting
-- function.
open SortNat

test = sort (suc zero :: zero :: suc (suc zero) :: nil)

