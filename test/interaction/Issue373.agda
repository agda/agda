module Issue373 where

data ⊤ : Set where
    tt : ⊤

{-# COMPILED_DATA ⊤ () () #-}

data ℕ : Set where
  zero : ℕ
  suc  : (n : ℕ) → ℕ

{-# BUILTIN NATURAL ℕ    #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}
{-# IMPORT Imports.Nat #-}
{-# COMPILED_DATA ℕ Imports.Nat.Nat Imports.Nat.Zero Imports.Nat.Suc #-}

data List (A : Set) : Set where
  []   : List A
  _∷_ : A → List A → List A

{-# BUILTIN LIST List #-}
{-# BUILTIN NIL  []   #-}
{-# BUILTIN CONS _∷_  #-}
{-# COMPILED_DATA List [] [] (:) #-}

postulate
  String : Set

{-# BUILTIN STRING String #-}
{-# COMPILED_TYPE String String #-}

postulate
  IO : Set → Set

{-# BUILTIN IO IO #-}
{-# COMPILED_TYPE IO IO #-}

infixl 1 _>>=_

postulate
  _>>=_ : ∀ {A B} → IO A → (A → IO B) → IO B

{-# COMPILED _>>=_ (\_ _ -> (>>=) :: IO a -> (a -> IO b) -> IO b) #-}

postulate
  putStrLn : String → IO ⊤

{-# COMPILED putStrLn putStrLn #-}

f : ℕ → String
f zero = "bad"
f _    = "ok"

-- Works:

-- main = putStrLn (f (suc zero))

-- Compiles, but when the program is run we (used to) get the output
-- "bad":

main = putStrLn (f 1)
