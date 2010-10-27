module RTP where
import RTS
import Prelude ((.), Eq, (==), Show, show)
import qualified Prelude hiding ((.), Eq, (==))

import Data.Char

-- import qualified RTS

undefined = Prelude.undefined

data Nat = Zero | Suc Nat

data Bool = False | True

type Float = Prelude.Double
-- newtype Float = FloatT { unboxFloat :: Prelude.Float}
newtype Char = CharT { unboxChar :: Prelude.Char } deriving (Prelude.Eq)

_Integer = ()
_Float = ()
_String =  ()
_Char = ()

_primShowBool :: Bool -> Prelude.String
_primShowBool False = "False"
_primShowBool True = "True"

_primShowInteger :: Prelude.Integer -> Prelude.String
_primShowInteger = Prelude.show

_primIntZero :: Prelude.Integer
_primIntZero = (0::Prelude.Integer)

_primIntOne :: Prelude.Integer
_primIntOne = (1::Prelude.Integer)

_primIntAdd :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
_primIntAdd = (Prelude.+)

_primIntSub :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
_primIntSub = (Prelude.-)


_primIntMul :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
_primIntMul = (Prelude.*)

_primIntDiv :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
_primIntDiv = (Prelude.div)

_primIntMod :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
_primIntMod = (Prelude.mod)

_primIntEquality :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
_primIntEquality = (Prelude.==)

_primIntLess :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
_primIntLess = (Prelude.<)

_int = _primNatToInteger
_primNatToInteger Zero = (0::Prelude.Integer)
_primNatToInteger (Suc n) = ( _primIntAdd (1::Prelude.Integer)  ( (_primNatToInteger(cast n))))

_primIntegerAbs 0 = zero
_primIntegerAbs n | (Prelude.>) n (0 :: Prelude.Integer) = suc (cast (_primIntegerAbs (  _primIntSub n (1::Prelude.Integer))))
	| Prelude.otherwise = _primIntegerAbs (_primIntSub 0 n)
_abs = _primIntegerAbs

_primIntegerToNat n = _primIntegerAbs n

_primShowFloat :: Float -> Prelude.String
_primShowFloat f = Prelude.show f
-- _primShowFloat (FloatT f) = Prelude.show f

_primShowChar c = [ unboxChar c]

_primCharEquality c1 c2 = c1 == c2
_primIsLower = isLower . unboxChar
_primIsDigit = isDigit . unboxChar
_primIsAlpha = isAlpha . unboxChar
_primIsSpace = isSpace . unboxChar
_primIsAscii = isAscii . unboxChar
_primIsLatin1 = isLatin1 . unboxChar
_primIsPrint = isPrint . unboxChar
_primIsHexDigit = isHexDigit . unboxChar
_primToUpper = toUpper . unboxChar
_primToLower = toLower . unboxChar
_primCharToNat = CharT . chr
_primNatToChar = ord . unboxChar

_primStringAppend :: Prelude.String -> Prelude.String -> Prelude.String
_primStringAppend = (Prelude.++)

_primStringEquality :: Prelude.String -> Prelude.String -> Prelude.Bool
_primStringEquality = (Prelude.==)

_primShowString :: Prelude.String -> Prelude.String
_primShowString s = show s

_primStringReverse = Prelude.reverse
_primStringToList s = Prelude.map CharT s
_primStringFromList s = Prelude.map unboxChar s

_primNatPlus m n = _abs (_primIntAdd (_int m) (_int n))
_primNatMinus m n = _abs (_primIntSub (_int m) (_int n))
_primNatTimes m n = _abs (_primIntMul (_int m) (_int n))
_primNatDivSuc m n= _abs (_primIntDiv (_int m) (_int n))
_primNatModSuc m n = _abs (_primIntMod (_int m) (_int n))
_primNatLess m n = _primIntLess (_int m) (_int n)
_primNatEquality m n = _primIntEquality (_int m) (_int n)

-- For tests
zero = Zero
suc = Suc
one = suc zero
two = suc one
