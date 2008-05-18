module RTP where
import RTS
import qualified RTN
import qualified Prelude


-- import qualified RTS

undefined = Prelude.undefined
data Bool = False | True

type Float = Prelude.Double
-- newtype Float = FloatT { unboxFloat :: Prelude.Float}
newtype Char = CharT { unboxChar :: Prelude.Char }

_Int = ()
_Float = ()
_String =  ()
_Char = ()

_primShowBool :: Bool -> Prelude.String
_primShowBool False = "False"
_primShowBool True = "True"

_primShowInt :: Prelude.Int -> Prelude.String
_primShowInt = Prelude.show

_primIntZero :: Prelude.Int 
_primIntZero = (0::Prelude.Int)

_primIntOne :: Prelude.Int 
_primIntOne = (1::Prelude.Int)

_primIntAdd :: Prelude.Int -> Prelude.Int -> Prelude.Int
_primIntAdd = (Prelude.+)

_primIntSub :: Prelude.Int -> Prelude.Int -> Prelude.Int
_primIntSub = (Prelude.-)


_primIntMul :: Prelude.Int -> Prelude.Int -> Prelude.Int
_primIntMul = (Prelude.*)

_primIntDiv :: Prelude.Int -> Prelude.Int -> Prelude.Int
_primIntDiv = (Prelude.div)

_primIntMod :: Prelude.Int -> Prelude.Int -> Prelude.Int
_primIntMod = (Prelude.mod)

_primIntEquals :: Prelude.Int -> Prelude.Int -> Prelude.Bool
_primIntEquals = (Prelude.==)

_primIntLess :: Prelude.Int -> Prelude.Int -> Prelude.Bool
_primIntLess = (Prelude.<)

_int = _primNatToInt
_primNatToInt RTN.C2 = (0::Prelude.Int)
_primNatToInt (RTN.C3 n) = ( _primIntAdd (1::Prelude.Int)  ( (_primNatToInt(cast n))))

_primIntToNat 0 = zero
_primIntToNat n | (Prelude.>) n (0 :: Prelude.Int) = suc (cast (_primIntToNat (  _primIntSub n (1::Prelude.Int))))
	| Prelude.otherwise = _primIntToNat (_primIntSub 0 n)
_abs = _primIntToNat

_primShowFloat :: Float -> Prelude.String
_primShowFloat f = Prelude.show f
-- _primShowFloat (FloatT f) = Prelude.show f

_primShowChar c = [ unboxChar c]

_primStringAppend :: Prelude.String -> Prelude.String -> Prelude.String
_primStringAppend = (Prelude.++)

_primStringReverse = Prelude.reverse
_primStringToList s = Prelude.map CharT s
_primStringFromList s = Prelude.map unboxChar s

_primNatPlus m n = _abs (_primIntAdd (_int m) (_int n))
_primNatMinus m n = _abs (_primIntSub (_int m) (_int n))
_primNatTimes m n = _abs (_primIntMul (_int m) (_int n))
_primNatDivSuc m n= _abs (_primIntDiv (_int m) (_int n))
_primNatModSuc m n = _abs (_primIntMod (_int m) (_int n))
_primNatLess m n = _primIntLess (_int m) (_int n)
_primNatEquals m n = _primIntEquals (_int m) (_int n)

-- For tests
zero = RTN.C2
suc = RTN.C3
one = suc zero
two = suc one

