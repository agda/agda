module Issue373 where

data ⊤ : Set where
    tt : ⊤

{-# COMPILE GHC ⊤ = data () (()) #-}

data ℕ : Set where
  zero : ℕ
  suc  : (n : ℕ) → ℕ

{-# BUILTIN NATURAL ℕ    #-}
{-# FOREIGN GHC import qualified Imports.Nat #-}

data List (A : Set) : Set where
  []   : List A
  _∷_ : A → List A → List A

{-# BUILTIN LIST List #-}
{-# BUILTIN NIL  []   #-}
{-# BUILTIN CONS _∷_  #-}
{-# COMPILE GHC List = data [] ([] | (:)) #-}

postulate
  String : Set

{-# BUILTIN STRING String #-}

postulate
  IO : Set → Set

{-# BUILTIN IO IO #-}
{-# COMPILE GHC IO = type IO #-}

infixl 1 _>>=_

postulate
  _>>=_ : ∀ {A B} → IO A → (A → IO B) → IO B

{-# COMPILE GHC _>>=_ = \_ _ -> (>>=) :: IO a -> (a -> IO b) -> IO b #-}

{-# FOREIGN GHC import qualified Data.Text.IO #-}

postulate
  putStrLn : String → IO ⊤

{-# COMPILE GHC putStrLn = Data.Text.IO.putStrLn #-}

f : ℕ → String
f zero = "bad"
f _    = "ok"

-- Works:

-- main = putStrLn (f (suc zero))

-- Compiles, but when the program is run we (used to) get the output
-- "bad":

main = putStrLn (f 1)
