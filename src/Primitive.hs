{-# LANGUAGE OverloadedStrings #-}
module Primitive
  ( axioms
  , primitives
  ) where

import Data.Map (Map)
import qualified Data.Map as Map
import Malfunction.AST

axioms :: Map String Term
axioms = Map.fromList
  [ notMapped "Char.Char"
  , notMapped "IO.IO"
  , notMapped "String.String"
  , notMapped "IsOne"
  , notMapped "IsOne1"
  , notMapped "IsOne2"
  , notMapped "isOneEmpty"
  , notMapped "itIsOne"
  , notMapped "Level"
  , notMapped "Bytes"
  , notMapped "eqBytes"
  , notMapped "append"
  , notMapped "empty"
  , notMapped "erasedBottom"
  , notMapped "Unsafe._.trustme"
  , notMapped "exitWith'"
  , notMapped "getArgs"
  , notMapped "getChar"
  , notMapped "getProgName"
  , notMapped "ioReturn"
  , notMapped "putChar"
  , "putStrLn" |-> Mglobal ["Pervasives", "print_string"]
  , "putStr"   |-> Mglobal ["Pervasives", "print_string"]
  , notMapped "ioBind"
  ]
  where
    notMapped n = (n, Mlambda [] $ errorT $ "Axiom not yet mapped: " ++ n)

primitives :: Map String Term
primitives = Map.fromList
  -- Integer functions
  [ "primIntegerPlus"     |-> binOp Add
  , "primIntegerMinus"    |-> binOp Sub
  , "primIntegerTimes"    |-> binOp Mul
  , "primIntegerDiv"      |-> binOp Div
  , "primIntegerMod"      |-> binOp Mod
  , "primIntegerEquality" |-> binOp Eq
  , "primIntegerLess"     |-> binOp Lt
  , notMapped "primIntegerAbs"
  , notMapped "primNatToInteger"
  , notMapped "primShowInteger"

  -- Natural number functions
  , "primNatPlus"         |-> binOp Add
  , "primNatMinus"        |-> binOp Sub
  , "primNatTimes"        |-> binOp Mul
  , "primNatDivSucAux"    |-> binOp Div
  , "primNatModSucAux"    |-> binOp Mod
  , "primNatEquality"     |-> binOp Eq
  , "primNatLess"         |-> binOp Lt

  -- Level functions
  , "primLevelZero"       |-> zeroT
  , "primLevelSuc"        |-> sucT
  , notMapped "primLevelMax"

  -- Floating point functions
  , notMapped "primNatToFloat"
  , notMapped "primFloatPlus"
  , notMapped "primFloatMinus"
  , notMapped "primFloatTimes"
  , notMapped "primFloatNegate"
  , notMapped "primFloatDiv"
  -- ASR (2016-09-29). We use bitwise equality for comparing Double
  -- because Haskell's Eq, which equates 0.0 and -0.0, allows to prove
  -- a contradiction (see Issue #2169).
  , notMapped "primFloatEquality"
  , notMapped "primFloatNumericalEquality"
  , notMapped "primFloatNumericalLess"
  , notMapped "primFloatSqrt"
  , notMapped "primRound"
  , notMapped "primFloor"
  , notMapped "primCeiling"
  , notMapped "primExp"
  , notMapped "primLog"
  , notMapped "primSin"
  , notMapped "primCos"
  , notMapped "primTan"
  , notMapped "primASin"
  , notMapped "primACos"
  , notMapped "primATan"
  , notMapped "primATan2"
  , notMapped "primShowFloat"

  -- Character functions
  , notMapped "primCharEquality"
  , notMapped "primIsLower"
  , notMapped "primIsDigit"
  , notMapped "primIsAlpha"
  , notMapped "primIsSpace"
  , notMapped "primIsAscii"
  , notMapped "primIsLatin1"
  , notMapped "primIsPrint"
  , notMapped "primIsHexDigit"
  , notMapped "primToUpper"
  , notMapped "primToLower"
  , notMapped "primCharToNat"
  , notMapped "primNatToChar"
  , notMapped "primShowChar"

  -- String functions
  , notMapped "primStringToList"
  , notMapped "primStringFromList"
  , notMapped "primStringAppend"
  , notMapped "primStringEquality"
  , notMapped "primShowString"

  -- Other stuff
  , notMapped "primTrustMe"
    -- This needs to be force : A → ((x : A) → B x) → B x rather than seq because of call-by-name.
  , notMapped "primForce"
  , notMapped "primForceLemma"
  , notMapped "primQNameEquality"
  , notMapped "primQNameLess"
  , notMapped "primShowQName"
  , notMapped "primQNameFixity"
  , notMapped "primMetaEquality"
  , notMapped "primMetaLess"
  , notMapped "primShowMeta"
  ]
  where
    notMapped n = (n, Mlambda [] $ errorT $ "Primitive not yet mapped: " ++ n)

(|->) :: a -> b -> (a, b)
(|->) = (,)

binOp :: BinaryIntOp -> Term
binOp op = Mlambda ["a", "b"] (Mintop2 op TInt (Mvar "a") (Mvar "b"))

zeroT :: Term
zeroT = Mint (CInt 0)
sucT :: Term
sucT = Mlambda ["a"] (Mintop2 Add TInt (Mvar "a") (Mint (CInt 1)))

-- FIXME: Copied from `Compiler` due to an otherwise cyclic dependency
errorT :: String -> Term
errorT err = Mapply (Mglobal ["Pervasives", "failwith"]) [Mstring err]
