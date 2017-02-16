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
  , "primIntegerAbs"      |-> errorT -- Probably needs to call OCaml
  , "primNatToInteger"    |-> errorT
  , "primShowInteger"     |-> errorT

  -- Natural number functions
  , "primNatPlus"         |-> errorT
  , "primNatMinus"        |-> errorT
  , "primNatTimes"        |-> errorT
  , "primNatDivSucAux"    |-> errorT
  , "primNatModSucAux"    |-> errorT
  , "primNatEquality"     |-> errorT
  , "primNatLess"         |-> errorT

  -- Level functions
  , "primLevelZero"       |-> errorT
  , "primLevelSuc"        |-> errorT
  , "primLevelMax"        |-> errorT

  -- Floating point functions
  , "primNatToFloat"      |-> errorT
  , "primFloatPlus"       |-> errorT
  , "primFloatMinus"      |-> errorT
  , "primFloatTimes"      |-> errorT
  , "primFloatNegate"     |-> errorT
  , "primFloatDiv"        |-> errorT
  -- ASR (2016-09-29). We use bitwise equality for comparing Double
  -- because Haskell's Eq, which equates 0.0 and -0.0, allows to prove
  -- a contradiction (see Issue #2169).
  , "primFloatEquality"   |-> errorT
  , "primFloatNumericalEquality" |-> errorT
  , "primFloatNumericalLess"     |-> errorT
  , "primFloatSqrt"       |-> errorT
  , "primRound"           |-> errorT
  , "primFloor"           |-> errorT
  , "primCeiling"         |-> errorT
  , "primExp"             |-> errorT
  , "primLog"             |-> errorT
  , "primSin"             |-> errorT
  , "primCos"             |-> errorT
  , "primTan"             |-> errorT
  , "primASin"            |-> errorT
  , "primACos"            |-> errorT
  , "primATan"            |-> errorT
  , "primATan2"           |-> errorT
  , "primShowFloat"       |-> errorT

  -- Character functions
  , "primCharEquality"    |-> errorT
  , "primIsLower"         |-> errorT
  , "primIsDigit"         |-> errorT
  , "primIsAlpha"         |-> errorT
  , "primIsSpace"         |-> errorT
  , "primIsAscii"         |-> errorT
  , "primIsLatin1"        |-> errorT
  , "primIsPrint"         |-> errorT
  , "primIsHexDigit"      |-> errorT
  , "primToUpper"         |-> errorT
  , "primToLower"         |-> errorT
  , "primCharToNat"       |-> errorT
  , "primNatToChar"       |-> errorT
  , "primShowChar"        |-> errorT

  -- String functions
  , "primStringToList"    |-> errorT
  , "primStringFromList"  |-> errorT
  , "primStringAppend"    |-> errorT
  , "primStringEquality"  |-> errorT
  , "primShowString"      |-> errorT

  -- Other stuff
  , "primTrustMe"         |-> errorT
    -- This needs to be force : A → ((x : A) → B x) → B x rather than seq because of call-by-name.
  , "primForce"           |-> errorT
  , "primForceLemma"      |-> errorT
  , "primQNameEquality"   |-> errorT
  , "primQNameLess"       |-> errorT
  , "primShowQName"       |-> errorT
  , "primQNameFixity"     |-> errorT
  , "primMetaEquality"    |-> errorT
  , "primMetaLess"        |-> errorT
  , "primShowMeta"        |-> errorT
  ]
  where
    (|->) = (,)

errorT :: Term
errorT = Mapply (Mglobal ["Pervasives", "failwith"]) [Mstring "Primitive function not implemented"]

binOp :: BinaryIntOp -> Term
binOp op = Mlambda ["a", "b"] (Mintop2 op TInt (Mvar "a") (Mvar "b"))
