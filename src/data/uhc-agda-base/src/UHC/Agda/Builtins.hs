module UHC.Agda.Builtins
  ( -- Integer
    primShowInteger
  , primIntegerDiv
  , primIntegerMod
  , primIntegerMinus
  , primIntegerPlus
  , primIntegerGreaterOrEqual
  , primIntegerEquality
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
  , primNatDivSuc
  , primNatDivSucAux
  , primNatModSuc
  , primNatModSucAux
    -- IO
  , primReturn
  , primBind
  , primGetContents
  , primReadFile
  , primWriteFile
  , primAppendFile
  , primPutStr
  , primPutStrLn
  , primReadFiniteFile
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
  , primIsLower
  , primIsDigit
  , primIsAlpha
  , primIsSpace
  , primIsAscii
  , primIsLatin1
  , primIsPrint
  , primIsHexDigit
  , primToUpper
  , primToLower
  , primNatToChar
    -- Float
  , primShowFloat
  , primMkFloat
  , primFloatEquality
    -- Reflection
  , QName (..)
  , primMkQName
  , primQNameEquality
  , primQNameLess
  , primShowQName
  , primQNameType
  , primQNameDefinition
  , primDataConstructors
  , primDataNumberOfParameters

    -- Debugging
  , primTrace

    -- Misc
  , primIfThenElse
  , unit
  )
where

import Prelude
import qualified Data.Char as C
import Debug.Trace
import UHC.OldException (onException)
import System.IO (openFile, IOMode (ReadMode), hClose, hFileSize, hGetContents)


-- internal helper for this file
notImplError :: String -> a
notImplError f = error $ "Feature " ++ f ++ " is not implemented in the UHC backend!"


-- ====================
-- Integer
-- ====================

primShowInteger :: Integer -> String
primShowInteger = show

primIntegerDiv :: Integer -> Integer -> Integer
primIntegerDiv = div

primIntegerMod :: Integer -> Integer -> Integer
primIntegerMod = mod

primIntegerMinus :: Integer -> Integer -> Integer
primIntegerMinus = (-)

primIntegerPlus :: Integer -> Integer -> Integer
primIntegerPlus = (+)

primIntegerGreaterOrEqual :: Integer -> Integer -> Bool
primIntegerGreaterOrEqual = (>=)

primIntegerEquality :: Integer -> Integer -> Bool
primIntegerEquality = (==)

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
-- Nat
-- ====================

-- In the long term, we should either make sure that uhc optimizes Nats to Integers
-- or do something clever here

type Nat = Integer

primNatToInteger :: Nat -> Integer
primNatToInteger = id

primIntegerToNat :: Integer -> Nat
primIntegerToNat = id

primNatPlus :: Nat -> Nat -> Nat
primNatPlus = (+)

primNatTimes :: Nat -> Nat -> Nat
primNatTimes = (*)

primNatMinus :: Nat -> Nat -> Nat
primNatMinus x y = max 0 (x - y)

primNatDivSuc :: Nat -> Nat -> Nat
primNatDivSuc x y = div x (y + 1)

primNatDivSucAux :: Nat -> Nat -> Nat -> Nat -> Nat
primNatDivSucAux k m n j = k + div (max 0 $ n + m - j) (m + 1)

primNatModSuc :: Nat -> Nat -> Nat
primNatModSuc x y = mod x (y + 1)

primNatModSucAux :: Nat -> Nat -> Nat -> Nat -> Nat
primNatModSucAux k m n j = if n > j then mod (n - j - 1) (m + 1) else k + n


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

primReadFiniteFile :: FilePath -> IO String
primReadFiniteFile f = do
  h <- openFile f ReadMode
  hFileSize h `onException` hClose h
  hGetContents h

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
primCharToNat c = primIntegerToNat (fromIntegral (fromEnum c))

primNatToChar :: Nat -> Char
primNatToChar i = toEnum (fromInteger (primNatToInteger i))

primCharEquality :: Char -> Char -> Bool
primCharEquality = (==)

primShowChar :: Char -> String
primShowChar c = show c

primIsLower     :: Char -> Bool
primIsLower     = C.isLower

primIsDigit     :: Char -> Bool
primIsDigit     = C.isDigit

primIsAlpha     :: Char -> Bool
primIsAlpha     = C.isAlpha

primIsSpace     :: Char -> Bool
primIsSpace     = C.isSpace

primIsAscii     :: Char -> Bool
primIsAscii     = C.isAscii

primIsLatin1    :: Char -> Bool
primIsLatin1    = C.isLatin1

primIsPrint     :: Char -> Bool
primIsPrint     = C.isPrint

primIsHexDigit  :: Char -> Bool
primIsHexDigit  = C.isHexDigit

primToUpper     :: Char -> Char
primToUpper     = C.toUpper

primToLower     :: Char -> Char
primToLower     = C.toLower

-- ====================
-- Float
-- ====================
primShowFloat :: Double -> String
-- GHC drops trailing zeroes, UHC doesn't seem to do so. Quick fix for now...
primShowFloat x
  | isNegativeZero x = "0.0"
  | otherwise        = reverse . dropWhile (=='0') . reverse $ show x

primMkFloat :: String -> Double
primMkFloat = read

primFloatEquality :: Double -> Double -> Bool
primFloatEquality x y
  | isNaN x && isNaN y = True
  | otherwise          = x == y

-- ====================
-- Reflection
-- ====================
data QName = QName { nameId, moduleId ::Integer, qnameString :: String }

primMkQName :: Integer -> Integer -> String -> QName
primMkQName = QName

instance Eq QName where
  (QName a b _) == (QName c d _) = (a, b) == (c, d)
instance Ord QName where
  compare (QName a b _) (QName c d _) = compare (a, b) (c, d)

primQNameEquality :: QName -> QName -> Bool
primQNameEquality = (==)

primQNameLess :: QName -> QName -> Bool
primQNameLess = (<)

primShowQName :: QName -> String
primShowQName = qnameString

primQNameType :: a
primQNameType = notImplError "primQNameType"

primQNameDefinition :: a
primQNameDefinition = notImplError "primQNameDefinition"

primDataConstructors :: a
primDataConstructors = notImplError "primDataConstructors"

primDataNumberOfParameters :: a
primDataNumberOfParameters = notImplError "primDataNumberOfParameters"

-- ====================
-- Debugging
-- ====================
primTrace :: String -> b -> b
primTrace = trace

-- ====================
-- Misc
-- ====================

primIfThenElse :: Bool -> a -> a -> a
primIfThenElse c t e = if c then t else e

-- | Unit wrapper function (instead of dropping a dummy function inside each module).
unit :: ()
unit = ()
