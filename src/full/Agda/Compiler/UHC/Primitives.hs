{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE CPP #-}
-- | Defines some primitive functions.
module Agda.Compiler.UHC.Primitives
  ( primFunctions
  )
where

import Agda.Compiler.UHC.AuxAST
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

-- | Primitives defined for the UHC backend. Maps primitive names to the core expression to be used as function body.
primFunctions :: M.Map String ((CompileT TCM) CExpr)
primFunctions = M.fromList $
    [(n, return $ mkVar (mkHsName ["UHC", "Agda", "Builtins"] n)) | n <-
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
        ]
    ] ++ [
        ("primTrustMe", mkTrustMe)
    ]
  where mkTrustMe = do
            -- lookup refl constructor
            bt <- fromMaybe __IMPOSSIBLE__ <$> (lift $ getBuiltin' builtinRefl)
            let reflNm = case T.ignoreSharing bt of
                    (T.Con conHd []) -> T.conName conHd
                    _                -> __IMPOSSIBLE__

            mkVar <$> getConstrFun reflNm

