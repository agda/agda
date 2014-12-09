{-# LANGUAGE CPP #-}
-- | Defines some primitive and builtin functions/datatypes.
module Agda.Compiler.UHC.Primitives
  ( primFunctions
  , BuiltinCache (..)
  , getBuiltins
  , isBuiltin
  , builtinUnitCtor
  )
where

import Data.List
import Agda.Compiler.UHC.CoreSyntax
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import qualified Agda.Syntax.Internal as T

#include "undefined.h"
import Agda.Utils.Impossible


import Control.Applicative
import qualified Data.Map as M
import Data.Maybe

import UHC.Light.Compiler.Core.API

-- | Primitives defined for the UHC backend. Maps primitive names to the AName of the function to call.
primFunctions :: M.Map String HsName
primFunctions = M.fromList
    [(n, mkHsName ["UHC", "Agda", "Builtins"] n) | n <-
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
        , "primNatToInteger"
        , "primIntegerToNat"
        -- String
        , "primStringAppend"
        , "primStringEquality"
        , "primStringFromList"
        , "primStringToList"
        -- Char
        , "primCharToNat"
        , "primCharEquality"
        -- Float
        , "primShowFloat"
        ]
    ]


type BuiltinName = String

data BuiltinCache
  = BuiltinCache
    { btccCtors :: M.Map T.QName (BuiltinName, CTag)
    , btccTys   :: M.Map T.QName (BuiltinName, Maybe HsName) -- unit has no core-level datatype
    }

isBuiltin :: BuiltinCache -> T.QName -> Bool
isBuiltin btins qnm = qnm `M.member` (btccCtors btins) || qnm `M.member` (btccTys btins)

-- | Returns the defined builtins.
--
-- If the constructors are defined for a builtin, the builtin for the corresponding
-- is guarantueed to be defined too.
getBuiltins :: (HasBuiltins m, MonadTCM m) => m BuiltinCache
getBuiltins = BuiltinCache
    <$> (mapM btinCtorToQName btinCtors >>= return . M.fromList . catMaybes)
    <*> (mapM btinTyToQName btinTys >>= return . M.fromList . catMaybes)
  where btinCtors :: [(String, CTag)]
        btinCtors = concatMap (\(a,b,c) -> c) btinTys
        btinTys :: [(String, Maybe HsName, [(String, CTag)])]
        btinTys = map (\(btin, dtNm, cons) ->
                            (btin, Just (mkHsName1 dtNm), map (\(cbtin, cNm, cTag, cArity) ->
                                    (cbtin, mkCTag (mkHsName1 dtNm) (mkHsCtorNm dtNm cNm) cTag cArity)) cons)
                      ) btinAgdaTys
                    ++ map (\(btin, cons) -> (btin, ctagDataTyNm $ snd $ head cons, cons)) btinHsTys
        btinAgdaTys =
          [ (builtinNat, "UHC.Agda.Builtins.Nat",
                [ (builtinSuc, "Suc", 0, 1)
                , (builtinZero, "Zero", 1, 0)
                ])
          ]
        btinHsTys =
          [ (builtinBool, 
                [ (builtinTrue, ctagTrue defaultEHCOpts)
                , (builtinFalse, ctagFalse defaultEHCOpts)
                ])
          -- TODO are we actually guarantueed that the Agda List type always has a suitable definition?
          -- if not, we should instead use COMPILED_CORE pragmas.
          , (builtinList,
                [ (builtinNil,    ctagNil defaultEHCOpts)
                , (builtinCons,   ctagCons defaultEHCOpts)
                ])
          , (builtinUnit, [(builtinUnitCons, ctagUnit)])
          ]
        btinToQName f (b, sp) = do
            bt <- getBuiltin' b
--            liftIO $ putStrLn $ show b ++ " - " ++ show bt
            return $ maybe Nothing (\x -> Just (x, (b, sp))) (f bt)
        btinCtorToQName = btinToQName (maybe Nothing (\x -> case T.ignoreSharing x of
            (T.Con conHd []) -> Just (T.conName conHd)
            _                -> __IMPOSSIBLE__
            ))
        btinTyToQName (a,b,c) = btinToQName (maybe Nothing (\x -> case T.ignoreSharing x of
            -- TODO should we allow elims?
            (T.Def nm [])    -> Just nm
            _                -> __IMPOSSIBLE__
            )) (a,b)
        ctagDataTyNm :: CTag -> Maybe HsName
        ctagDataTyNm = destructCTag Nothing (\dt _ _ _ -> Just dt)
        -- hs generated constructor are not datatype-prefixed
        mkHsCtorNm :: String -> String -> HsName
        mkHsCtorNm dt con = mkHsName1 ((dropWhileEnd (/='.') dt) ++ con)

builtinUnitCtor :: HsName
builtinUnitCtor = mkHsName1 "UHC.Agda.Builtins.unit"
