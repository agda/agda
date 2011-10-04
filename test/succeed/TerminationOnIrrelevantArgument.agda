-- Andreas, 2011-10-03
-- Defining a universe for dependent types
-- where the El function only depends on the type code but not on its
-- proof of well-formedness
{-# OPTIONS --experimental-irrelevance #-}
module TerminationOnIrrelevantArgument where

data ⊥ : Set where

data D : Set where
  empty : D
  pi    : D -> D -> D
  other : D

postulate
  app : D -> D -> D

mutual

  data Ty : D -> Set where

    Empty : Ty empty

    Pi    : (a f : D) ->
            (A : Ty a) ->
            (F : (d : D) -> .(El a A d) -> Ty (app f d)) ->
            Ty (pi a f) 
  

  El : (a : D) -> .(A : Ty a) -> D -> Set
  El  empty    Empty         g = ⊥
  El (pi a f) (Pi .a .f A F) g = (d : D) -> .(Ad : El a A d) -> 
                                 El (app f d) (F d Ad) (app g d)
  El  other   ()             g

-- Termination checking needs to look inside irrelevant arguments.
-- This only works because the termination checker is syntactic
-- and does not respect equality of irrelevant things!

-- clearly, the derivation of Ty a does not matter when computing El
cast : (a : D)(A A' : Ty a)(d : D) -> El a A d -> El a A' d
cast a A A' d x = x
