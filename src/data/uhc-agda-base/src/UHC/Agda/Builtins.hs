module UHC.Agda.Builtins
  ( Nat (..)
  , primIntegerToNat
  , primPutStrLn
  , primReturn
  , primBind
  )
where

import Prelude

-- In the long term, we should either make sure that uhc optimizes Nats to Integers
-- or do something clever here

data Nat = Zero | Suc Nat

primIntegerToNat :: Integer -> Nat
primIntegerToNat i | i < 0  = error "Negative integers cannot be converted to Nat."
primIntegerToNat i | i == 0 = Zero
primIntegerToNat i | i > 0  = Suc (primIntegerToNat (i - 1))


-- Calling haskell functions with class constraints from Agda
-- isn't supported yet, so just remove the class constraints on return/bind

primPutStrLn :: String -> IO ()
primPutStrLn = putStrLn

primReturn :: a -> IO a
primReturn = return

primBind :: IO a -> (a -> IO b) -> IO b
primBind = (>>=)

-- TODO this is a work around, as we don't have proper linking for core modules yet
main :: IO ()
main = Zero `seq` Suc `seq` primIntegerToNat `seq` primPutStrLn `seq` primReturn `seq` primBind `seq` primDebugNatToInteger
       `seq` primDebugIntegerToString `seq` return ()

-- TODO should this actually be a prim? if so, rename
primDebugNatToInteger :: Nat -> Integer
primDebugNatToInteger (Zero) = 0
primDebugNatToInteger (Suc n) = 1 + primDebugNatToInteger n

-- TODO should this actually be a prim? if so, rename
primDebugIntegerToString :: Integer -> String
primDebugIntegerToString i = show i
