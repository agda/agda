{-# LANGUAGE CPP #-}

module Agda.Compiler.UHC.Primitives
  ( primFunctions
  , BuiltinCache (..)
  , BuiltinConSpec (..)
  , getBuiltins
  , builtinConSpecToCoreConstr )
where

import Agda.Compiler.UHC.Interface
import Agda.Compiler.UHC.CoreSyntax
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import qualified Agda.Syntax.Internal as T

#include "../../undefined.h"
import Agda.Utils.Impossible


import Control.Applicative
import Data.Map as M
import Data.Maybe (catMaybes)

-- | Primitives defined for the UHC backend. Maps primitive names to the AName of the function to call.
primFunctions :: Map String AName
primFunctions = M.fromList
    [(n, ANmCore $ "UHC.Agda.Builtins." ++ n) | n <-
        [
        -- String
          "primStringAppend"
        , "primStringEquality"
        -- Char
        , "primCharToNat"
        , "primCharEquality"
        ]
    ]


data BuiltinConSpec
  = ConNamed { conSpecDt :: String, conSpecCtor :: String, conSpecTag :: Int }
  | ConUnit

data BuiltinCache
  = BuiltinCache
    { btccCtors :: M.Map T.QName BuiltinConSpec
    , btccTys   :: M.Map T.QName ()
    }

getBuiltins :: (HasBuiltins m, MonadTCM m) => m BuiltinCache
getBuiltins = BuiltinCache
    <$> (mapM btinCtorToQName btinCtors >>= return . M.fromList . catMaybes)
    <*> (mapM btinTyToQName btinTys >>= return . M.fromList . catMaybes)
  where btinTys   =
          [ (builtinNat,    ())
          , (builtinList,   ())
          , (builtinBool,   ())
          , (builtinUnit,   ())
          ]
        btinCtors =
          [ (builtinSuc,    (ConNamed "UHC.Agda.Builtins.Nat" "Suc" 0))
          , (builtinZero,   (ConNamed "UHC.Agda.Builtins.Nat" "Zero" 1))
--          TODO the Agda List type takes a type argument, Haskells doesn't
--          , (builtinNil,    (ConNamed "UHC.Base.[]" "[]" 1))
--          , (builtinCons,   (ConNamed "UHC.Base.[]" ":" 0))
          , (builtinTrue,   (ConNamed "UHC.Base.Bool" "True" 1))
          , (builtinFalse,  (ConNamed "UHC.Base.Bool" "False" 0))
          , (builtinUnitCons, (ConUnit))
          ]
        btinToQName f (b, sp) = do
            bt <- getBuiltin' b
--            liftIO $ putStrLn $ show b ++ " - " ++ show bt
            return $ maybe Nothing (\x -> Just (x, sp)) (f bt)
        btinCtorToQName = btinToQName (\x -> case x of
            (Just (T.Con conHd [])) -> Just (T.conName conHd)
            _                       -> Nothing
            )
        btinTyToQName = btinToQName (\x -> case x of
            -- TODO should we allow elims?
            (Just (T.Def nm []))    -> Just nm
            _                       -> Nothing
            )

builtinConSpecToCoreConstr :: BuiltinConSpec -> CoreConstr
builtinConSpecToCoreConstr (ConNamed dt ctor tag) = (dt, ctor, tag)
builtinConSpecToCoreConstr (ConUnit) = __IMPOSSIBLE__

