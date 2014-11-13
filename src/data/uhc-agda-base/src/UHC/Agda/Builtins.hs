module UHC.Agda.Builtins
  ( -- Temp Debug
    primDebugNatToInteger
  , primDebugIntegerToString
    --  Nat
  , Nat (..)
  , primIntegerToNat
    -- IO
  , primPutStrLn
  , primReturn
  , primBind
    -- String
  , primStringAppend
  , primStringEquality
    -- Char
  , primCharToNat
  , primCharEquality
  )
where

import Prelude
-- ====================
-- Temporary Debug Stuff
-- ====================

-- TODO should this actually be a prim? if so, rename
primDebugNatToInteger :: Nat -> Integer
primDebugNatToInteger (Zero) = 0
primDebugNatToInteger (Suc n) = 1 + primDebugNatToInteger n

-- TODO should this actually be a prim? if so, rename
primDebugIntegerToString :: Integer -> String
primDebugIntegerToString i = show i

-- ====================
-- Nat
-- ====================

-- In the long term, we should either make sure that uhc optimizes Nats to Integers
-- or do something clever here

data Nat = Zero | Suc Nat

primIntegerToNat :: Integer -> Nat
primIntegerToNat i | i < 0  = error "Negative integers cannot be converted to Nat."
primIntegerToNat i | i == 0 = Zero
primIntegerToNat i | i > 0  = Suc (primIntegerToNat (i - 1))

-- ====================
-- IO
-- ====================

-- Calling haskell functions with class constraints from Agda
-- isn't supported yet, so just remove the class constraints on return/bind

primPutStrLn :: String -> IO ()
primPutStrLn = putStrLn

primReturn :: a -> IO a
primReturn = return

primBind :: IO a -> (a -> IO b) -> IO b
primBind = (>>=)

-- ====================
-- String
-- ====================

primStringAppend :: String -> String -> String
primStringAppend = (++)

primStringEquality :: String -> String -> Bool
primStringEquality = (==)

-- ====================
-- Char
-- ====================

primCharToNat :: Char -> Nat
primCharToNat c = primIntegerToNat (read [c] :: Integer)

primCharEquality :: Char -> Char -> Bool
primCharEquality = (==)
