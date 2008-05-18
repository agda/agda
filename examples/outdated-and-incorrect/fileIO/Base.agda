
module Base where

postulate String : Set
          Char   : Set
{-# BUILTIN STRING String #-}
{-# BUILTIN CHAR   Char   #-}

data Unit : Set where
  unit : Unit

{-# COMPILED_DATA Unit () #-}

data Bool : Set where
  true  : Bool
  false : Bool

data False  : Set where
record True : Set where

IsTrue : Bool -> Set
IsTrue true = True
IsTrue false = False

{-# COMPILED_DATA Bool True False #-}

infixr 40 _::_
data List (A : Set) : Set where
  [] : List A
  _::_ : A -> List A -> List A

{-# COMPILED_DATA List [] (:) #-}

data _×_ (A B : Set) : Set where
  _,_ : A -> B -> A × B

{-# COMPILED_DATA _×_ (,) #-}