
module examples.Monad where

data Monad (M:Set -> Set) : Set1 where
  monad : ({A:Set} -> A -> M A)			  ->  -- return
	  ({A,B:Set} -> M A -> (A -> M B) -> M B) ->  -- bind
	  Monad M

monadReturn : {M:Set -> Set} -> Monad M -> {A:Set} -> A -> M A
monadReturn (monad ret bind) = ret

monadBind : {M:Set -> Set} -> Monad M -> {A,B:Set} -> M A -> (A -> M B) -> M B
monadBind (monad ret bind) = bind

module Monad {M:Set -> Set}(monadM:Monad M) where

  return : {A:Set} -> A -> M A
  return = monadReturn monadM

  (>>=) : {A,B:Set} -> M A -> (A -> M B) -> M B
  (>>=) = monadBind monadM




