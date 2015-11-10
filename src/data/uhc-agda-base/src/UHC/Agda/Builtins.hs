module UHC.Agda.Builtins
  ( -- Integer
    primShowInteger
  , primIntegerQuot
  , primIntegerRem
  , primIntegerMinus
  , primIntegerPlus
  , primIntegerTimes
  , primIntegerGreaterOrEqual
  , primIntegerEquality
  , primIntegerLess
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
  , primNatLess
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
  , primSeq
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

primIntegerQuot :: Integer -> Integer -> Integer
primIntegerQuot = quot

primIntegerRem :: Integer -> Integer -> Integer
primIntegerRem = rem

primIntegerMinus :: Integer -> Integer -> Integer
primIntegerMinus = (-)

primIntegerPlus :: Integer -> Integer -> Integer
primIntegerPlus = (+)

primIntegerTimes :: Integer -> Integer -> Integer
primIntegerTimes = (*)

primIntegerGreaterOrEqual :: Integer -> Integer -> Bool
primIntegerGreaterOrEqual = (>=)

primIntegerLess :: Integer -> Integer -> Bool
primIntegerLess = (<)

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

newtype Nat = Nat Integer

liftN2 :: (Integer -> Integer -> Integer) -> Nat -> Nat -> Nat
liftN2 f x y = Nat (f (unNat x) (unNat y))

unNat :: Nat -> Integer
unNat (Nat i) = i

primNatToInteger :: Nat -> Integer
primNatToInteger = unNat

-- unsafe!
primIntegerToNat :: Integer -> Nat
primIntegerToNat = Nat

primNatPlus :: Nat -> Nat -> Nat
primNatPlus = liftN2 (+)

primNatTimes :: Nat -> Nat -> Nat
primNatTimes = liftN2 (*)

primNatMinus :: Nat -> Nat -> Nat
primNatMinus x y = Nat $ max 0 (unNat x - unNat y)

primNatDivSuc :: Nat -> Nat -> Nat
primNatDivSuc x y = Nat $ div (unNat x) (unNat y + 1)

primNatDivSucAux :: Nat -> Nat -> Nat -> Nat -> Nat
primNatDivSucAux (Nat k) (Nat m) (Nat n) (Nat j) =
  Nat $ k + div (max 0 $ n + m - j) (m + 1)

primNatModSuc :: Nat -> Nat -> Nat
primNatModSuc x y = Nat $ mod (unNat x) (unNat y + 1)

primNatModSucAux :: Nat -> Nat -> Nat -> Nat -> Nat
primNatModSucAux (Nat k) (Nat m) (Nat n) (Nat j) =
  Nat $ if n > j then mod (n - j - 1) (m + 1) else k + n

primNatLess :: Nat -> Nat -> Bool
primNatLess x y = unNat x < unNat y

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

primSeq :: a -> b -> b
primSeq = seq

-- | Unit wrapper function (instead of dropping a dummy function inside each module).
unit :: ()
unit = ()
