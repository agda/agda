
module CompilingCoinduction where

open import Common.Coinduction

data List (A : Set) : Set where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A

{-# BUILTIN LIST List #-}
{-# BUILTIN NIL  []   #-}
{-# BUILTIN CONS _∷_  #-}

{-# COMPILED_DATA List [] [] (:) #-}

postulate
  Char : Set

{-# BUILTIN CHAR Char #-}
{-# COMPILED_TYPE Char Char #-}

-- Strings --

postulate
  String : Set

{-# BUILTIN STRING String #-}
{-# COMPILED_TYPE String String #-}

data Unit : Set where
  unit : Unit

{-# COMPILED_DATA Unit () () #-}

postulate
  IO : Set → Set

{-# COMPILED_TYPE IO IO #-}
{-# BUILTIN IO IO #-}

postulate
  putStrLn : ∞ String → IO Unit

{-# COMPILED putStrLn putStrLn #-}

main = putStrLn (♯ "a")
