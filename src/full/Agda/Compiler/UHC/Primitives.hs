{-# LANGUAGE CPP #-}
-- | Defines some primitive functions.
module Agda.Compiler.UHC.Primitives
  ( primFunNm
  , primFunctions
  )
where

import Agda.Compiler.UHC.CompileState
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import qualified Agda.Syntax.Internal as T
import Control.Monad.Trans

#include "undefined.h"
import Agda.Utils.Impossible

#if __GLASGOW_HASKELL__ <= 708
import Control.Applicative
#endif

import qualified Data.Map as M
import Data.Maybe

import Agda.Compiler.UHC.Bridge

primFunNm :: String -> HsName
primFunNm = mkHsName ["UHC", "Agda", "Builtins"]

-- | Primitives defined for the UHC backend. Maps primitive names to the core expression to be used as function body.
primFunctions :: M.Map String ((CompileT TCM) CExpr)
primFunctions = M.fromList $
    [(n, return $ mkVar (primFunNm n)) | n <-
        [
        -- Level
          "primLevelMax"
        , "primLevelZero"
        , "primLevelSuc"
        -- Integer
        , "primShowInteger"
        -- Nat
        , "primNatPlus"
        , "primNatTimes"
        , "primNatMinus"
        , "primNatDivSuc"
        , "primNatDivSucAux"
        , "primNatModSuc"
        , "primNatModSucAux"
        , "primNatToInteger"
        , "primNatEquality"
        , "primNatLess"
        , "primIntegerToNat"
        -- String
        , "primStringAppend"
        , "primStringEquality"
        , "primStringFromList"
        , "primStringToList"
        , "primShowString"
        -- Char
        , "primCharToNat"
        , "primCharEquality"
        , "primShowChar"
        , "primIsLower"
        , "primIsDigit"
        , "primIsAlpha"
        , "primIsSpace"
        , "primIsAscii"
        , "primIsLatin1"
        , "primIsPrint"
        , "primIsHexDigit"
        , "primToUpper"
        , "primToLower"
        , "primNatToChar"
        -- Float
        , "primShowFloat"
        , "primFloatEquality"
        , "primFloatNumericalEquality"
        , "primFloatNumericalLess"
        , "primNatToFloat"
        , "primFloatPlus"
        , "primFloatMinus"
        , "primFloatTimes"
        , "primFloatNegate"
        , "primFloatDiv"
        , "primFloatSqrt"
        , "primRound"
        , "primFloor"
        , "primCeiling"
        , "primExp"
        , "primLog"
        , "primSin"
        , "primCos"
        , "primTan"
        , "primASin"
        , "primACos"
        , "primATan"
        , "primATan"
        , "primATan2"
        -- Reflection
        , "primQNameEquality"
        , "primQNameLess"
        , "primShowQName"
        , "primQNameFixity"
        , "primMetaEquality"
        , "primMetaLess"
        , "primShowMeta"
        ]
    ] ++ [
        ("primTrustMe", mkTrustMe)
    ]
  where mkTrustMe = do
            -- lookup refl constructor
            bt <- fromMaybe __IMPOSSIBLE__ <$> (lift $ getBuiltin' builtinRefl)
            let reflNm = case T.ignoreSharing bt of
                    (T.Con conHd _ []) -> T.conName conHd
                    _                -> __IMPOSSIBLE__

            mkVar <$> getConstrFun reflNm
