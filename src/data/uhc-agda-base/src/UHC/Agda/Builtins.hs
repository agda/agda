module UHC.Agda.Builtins
  ( -- Integer
    primShowInteger
    -- Levels
  , primLevelZero
  , primLevelSuc
  , primLevelMax
    --  Nat
  , Nat (..)
  , primIntegerToNat
  , primNatToInteger
  , primNatMinus
  , primNatPlus
  , primNatTimes
    -- IO
  , primReturn
  , primBind
  , primGetContents
  , primReadFile
  , primWriteFile
  , primAppendFile
  , primPutStr
  , primPutStrLn
    -- String
  , primStringAppend
  , primStringEquality
  , primStringFromList
  , primStringToList
  , primShowString
    -- Char
  , primCharToNat
  , primCharEquality
  , primShowChar
    -- Float
  , primShowFloat
  , primMkFloat

    -- Debugging
  , primTrace

  , unit
  )
where

import Prelude
import Debug.Trace
-- ====================
-- Integer
-- ====================

primShowInteger :: Integer -> String
primShowInteger = show

-- ====================
-- Levels
-- ====================

primLevelZero :: ()
primLevelZero = ()

primLevelSuc :: () -> ()
primLevelSuc _ = ()

primLevelMax :: () -> () -> ()
primLevelMax _ _ = ()

-- ====================
-- Misc
-- ====================

-- | Unit wrapper function (instead of dropping a dummy function inside each module).
unit :: ()
unit = ()

-- ====================
-- Nat
-- ====================

-- In the long term, we should either make sure that uhc optimizes Nats to Integers
-- or do something clever here

data Nat = Zero | Suc Nat

primNatToInteger :: Nat -> Integer
primNatToInteger (Zero) = 0
primNatToInteger (Suc n) = 1 + primNatToInteger n

primIntegerToNat :: Integer -> Nat
primIntegerToNat i | i < 0  = error "Negative integers cannot be converted to Nat."
primIntegerToNat i | i == 0 = Zero
primIntegerToNat i | i > 0  = Suc (primIntegerToNat (i - 1))

primNatPlus :: Nat -> Nat -> Nat
primNatPlus Zero b = b
primNatPlus (Suc a) b = Suc (a `primNatPlus` b)

primNatTimes :: Nat -> Nat -> Nat
primNatTimes Zero b = Zero
primNatTimes (Suc a) b = (a `primNatTimes` b) `primNatPlus` b

primNatMinus :: Nat -> Nat -> Nat
primNatMinus a Zero = a
primNatMinus (Suc a) (Suc b) = a `primNatMinus` b
primNatMinus Zero _ = Zero

-- ====================
-- IO
-- ====================

-- Calling haskell functions with class constraints from Agda
-- isn't supported yet, so just remove the class constraints on return/bind

primReturn :: a -> IO a
primReturn = return

primBind :: IO a -> (a -> IO b) -> IO b
primBind = (>>=)

primGetContents :: IO String
primGetContents = getContents

primReadFile :: FilePath -> IO String
primReadFile = readFile

primWriteFile :: FilePath -> String -> IO ()
primWriteFile = writeFile

primAppendFile :: FilePath -> String -> IO ()
primAppendFile = appendFile

primPutStr :: String -> IO ()
primPutStr = putStr

primPutStrLn :: String -> IO ()
primPutStrLn = putStrLn


-- ====================
-- String
-- ====================

primStringFromList :: [Char] -> String
primStringFromList = id

primStringToList :: String -> [Char]
primStringToList = id

primStringAppend :: String -> String -> String
primStringAppend = (++)

primStringEquality :: String -> String -> Bool
primStringEquality = (==)

primShowString :: String -> String
primShowString = id

-- ====================
-- Char
-- ====================

primCharToNat :: Char -> Nat
primCharToNat c = primIntegerToNat (read [c] :: Integer)

primCharEquality :: Char -> Char -> Bool
primCharEquality = (==)

primShowChar :: Char -> String
primShowChar c = [c]

-- ====================
-- Float
-- ====================
primShowFloat :: Double -> String
-- GHC drops trailing zeroes, UHC doesn't seem to do so. Quick fix for now...
primShowFloat = reverse . dropWhile (=='0') . reverse . show

primMkFloat :: String -> Double
primMkFloat = read

-- ====================
-- Debugging
-- ====================
primTrace :: String -> b -> b
primTrace = trace
