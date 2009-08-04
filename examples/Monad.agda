
module Monad where

module Prelude where

  infixl 40 _∘_

  id : {A : Set} -> A -> A
  id x = x

  _∘_ : {A B C : Set} -> (B -> C) -> (A -> B) -> A -> C
  f ∘ g = \x -> f (g x)

  data Nat : Set where
    zero : Nat
    suc  : Nat -> Nat

module Base where

  data Monad (M : Set -> Set) : Set1 where
    monad : (return : {A : Set} -> A -> M A)                 ->
            (bind   : {A B : Set} -> M A -> (A -> M B) -> M B) ->
            Monad M

  monadReturn : {M : Set -> Set} -> Monad M -> {A : Set} -> A -> M A
  monadReturn (monad ret bind) = ret

  monadBind : {M : Set -> Set} -> Monad M -> {A B : Set} -> M A -> (A -> M B) -> M B
  monadBind (monad ret bind) = bind

module Monad {M : Set -> Set}(monadM : Base.Monad M) where

  open Prelude

  infixl 15 _>>=_

  -- Return and bind --------------------------------------------------------

  return : {A : Set} -> A -> M A
  return = Base.monadReturn monadM

  _>>=_ : {A B : Set} -> M A -> (A -> M B) -> M B
  _>>=_ = Base.monadBind monadM

  -- Other operations -------------------------------------------------------

  liftM : {A B : Set} -> (A -> B) -> M A -> M B
  liftM f m = m >>= return ∘ f

module List where

  infixr 20 _++_ _::_

  -- The list datatype ------------------------------------------------------

  data List (A : Set) : Set where
    nil  : List A
    _::_ : A -> List A -> List A

  -- Some list operations ---------------------------------------------------

  foldr : {A B : Set} -> (A -> B -> B) -> B -> List A -> B
  foldr f e nil     = e
  foldr f e (x :: xs) = f x (foldr f e xs)

  map : {A B : Set} -> (A -> B) -> List A -> List B
  map f nil     = nil
  map f (x :: xs) = f x :: map f xs

  _++_ : {A : Set} -> List A -> List A -> List A
  nil       ++ ys = ys
  (x :: xs) ++ ys = x :: (xs ++ ys)

  concat : {A : Set} -> List (List A) -> List A
  concat = foldr _++_ nil

  -- List is a monad --------------------------------------------------------

  open Base

  monadList : Monad List
  monadList = monad ret bind
    where
      ret : {A : Set} -> A -> List A
      ret x = x :: nil

      bind : {A B : Set} -> List A -> (A -> List B) -> List B
      bind xs f = concat (map f xs)

open Prelude
open List
module MonadList = Monad monadList
open MonadList

