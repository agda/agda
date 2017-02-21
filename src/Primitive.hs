module Primitive (compilePrim) where

import Data.Map (Map)
import qualified Data.Map as Map
import Malfunction.AST
import Compiler
import Agda.Compiler.Backend

compilePrim
  :: QName -- ^ The qname of the primitive
  -> String -- ^ The name of the primitive
  -> TCM (Maybe Binding)
compilePrim q s = return $ Named (nameToIdent q) <$> Map.lookup s primitiveFunctions

primitiveFunctions :: Map String Term
primitiveFunctions = Map.fromList

  -- Integer functions
  [ "primIntegerPlus"     |-> binOp Add
  , "primIntegerMinus"    |-> binOp Sub
  , "primIntegerTimes"    |-> binOp Mul
  , "primIntegerDiv"      |-> binOp Div
  , "primIntegerMod"      |-> binOp Mod
  , "primIntegerEquality" |-> binOp Eq
  , "primIntegerLess"     |-> binOp Lt
  , "primIntegerAbs"      |-> errorTPrim -- Probably needs to call OCaml
  , "primNatToInteger"    |-> errorTPrim
  , "primShowInteger"     |-> errorTPrim

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
  , "primLevelMax"        |-> errorTPrim

  -- Floating point functions
  , "primNatToFloat"      |-> errorTPrim
  , "primFloatPlus"       |-> errorTPrim
  , "primFloatMinus"      |-> errorTPrim
  , "primFloatTimes"      |-> errorTPrim
  , "primFloatNegate"     |-> errorTPrim
  , "primFloatDiv"        |-> errorTPrim
  -- ASR (2016-09-29). We use bitwise equality for comparing Double
  -- because Haskell's Eq, which equates 0.0 and -0.0, allows to prove
  -- a contradiction (see Issue #2169).
  , "primFloatEquality"   |-> errorTPrim
  , "primFloatNumericalEquality" |-> errorTPrim
  , "primFloatNumericalLess"     |-> errorTPrim
  , "primFloatSqrt"       |-> errorTPrim
  , "primRound"           |-> errorTPrim
  , "primFloor"           |-> errorTPrim
  , "primCeiling"         |-> errorTPrim
  , "primExp"             |-> errorTPrim
  , "primLog"             |-> errorTPrim
  , "primSin"             |-> errorTPrim
  , "primCos"             |-> errorTPrim
  , "primTan"             |-> errorTPrim
  , "primASin"            |-> errorTPrim
  , "primACos"            |-> errorTPrim
  , "primATan"            |-> errorTPrim
  , "primATan2"           |-> errorTPrim
  , "primShowFloat"       |-> errorTPrim

  -- Character functions
  , "primCharEquality"    |-> errorTPrim
  , "primIsLower"         |-> errorTPrim
  , "primIsDigit"         |-> errorTPrim
  , "primIsAlpha"         |-> errorTPrim
  , "primIsSpace"         |-> errorTPrim
  , "primIsAscii"         |-> errorTPrim
  , "primIsLatin1"        |-> errorTPrim
  , "primIsPrint"         |-> errorTPrim
  , "primIsHexDigit"      |-> errorTPrim
  , "primToUpper"         |-> errorTPrim
  , "primToLower"         |-> errorTPrim
  , "primCharToNat"       |-> errorTPrim
  , "primNatToChar"       |-> errorTPrim
  , "primShowChar"        |-> errorTPrim

  -- String functions
  , "primStringToList"    |-> errorTPrim
  , "primStringFromList"  |-> errorTPrim
  , "primStringAppend"    |-> errorTPrim
  , "primStringEquality"  |-> errorTPrim
  , "primShowString"      |-> errorTPrim

  -- Other stuff
  , "primTrustMe"         |-> errorTPrim
    -- This needs to be force : A → ((x : A) → B x) → B x rather than seq because of call-by-name.
  , "primForce"           |-> errorTPrim
  , "primForceLemma"      |-> errorTPrim
  , "primQNameEquality"   |-> errorTPrim
  , "primQNameLess"       |-> errorTPrim
  , "primShowQName"       |-> errorTPrim
  , "primQNameFixity"     |-> errorTPrim
  , "primMetaEquality"    |-> errorTPrim
  , "primMetaLess"        |-> errorTPrim
  , "primShowMeta"        |-> errorTPrim
  ]
  where
    (|->) = (,)

errorTPrim :: Term
errorTPrim
  | False = errorT "Primitive function not implemented"
  | otherwise = wildcardTerm

binOp :: BinaryIntOp -> Term
binOp op = Mlambda ["a", "b"] (Mintop2 op TInt (Mvar "a") (Mvar "b"))

zeroT :: Term
zeroT = Mint (CInt 0)
sucT :: Term
sucT = Mlambda ["a"] (Mintop2 Add TInt (Mvar "a") (Mint (CInt 1)))
