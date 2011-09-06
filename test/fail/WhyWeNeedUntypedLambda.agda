{- 2010-09-28 Andreas, see issue 336 -}

module WhyWeNeedUntypedLambda where

IdT = ({A : Set} -> A -> A)

data _==_ {A : Set2}(a : A) : A -> Set where
  refl : a == a

-- Untyped lambda succeeds, because checking \ x -> x : X is postponed, 
-- then the solution X = IdT is found, and upon revisiting the tc problem
-- a hidden lambda \ {A} is inserted.
foo : ({X : Set1} -> X -> X == IdT -> Set) -> Set
foo k = k (\ x -> x) refl         -- succeeds

{-
-- Typed lambda fails, because \ (x : _) -> x has inferred type ?A -> ?A
-- but then unification with IdT fails.
foo' : ({X : Set1} -> X -> X == IdT -> Set) -> Set
foo' k = k (\ (x : _) -> x) refl  -- fails
-}