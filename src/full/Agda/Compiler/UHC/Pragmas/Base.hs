{-# LANGUAGE CPP                #-}
{-# LANGUAGE DeriveDataTypeable #-}

-- | Defines UHC Core functions used in other parts of Agda.
-- E.g. parsing Core pragmas uses the `parseCoreCode` function.
module Agda.Compiler.UHC.Pragmas.Base
  ( CoreExpr,
    CoreType (..),
    CoreConstr (..),
    coreConstrToCTag,
    setTag,
    HsName
  )
where


import Data.Typeable
import qualified Data.Map as M

import Agda.Compiler.UHC.Bridge as CA
import Agda.Compiler.UHC.MagicTypes

#include "undefined.h"
import Agda.Utils.Impossible



data CoreType
  = CTMagic MagicName -- ^ Magic name
  | CTNormal String -- Core Datatype name
  deriving (Eq, Show, Typeable)

-- We store the COMPILED_UHC pragmas as string,
-- as storing the UHC AST makes the serialization
-- format dependent on uhc-light. This also makes it
-- possible to just store COMPILED_UHC pragmas unchecked
-- in the interface file, if the UHC backend is disabled.
type CoreExpr = String

-- We need an explicit representation for constructors, as we need to serialise the CoreConstr
-- to store it inside agdai files. Else we could just use a partially applied
-- CTag constructor instead (we don't know the arity yet...).
data CoreConstr
  = CCMagic MagicName MagicName -- Magic type constructor with fixed arity; (datatype, ctor)
  | CCNormal HsName HsName Int -- Normall UHC Core Constructor; (datatype, constr, tag)
  deriving (Eq, Show, Typeable)


setTag :: CoreConstr -> Int -> CoreConstr
setTag (CCNormal a b _) t = CCNormal a b t
setTag _ _ = __IMPOSSIBLE__

coreConstrToCTag :: CoreConstr
    -> Int -- ^ Arity
    -> CTag
coreConstrToCTag (CCMagic dtMgcNm conMgcNm) _ = conMp M.! conMgcNm
  where (_, conMp) = getMagicTypes M.! dtMgcNm
coreConstrToCTag (CCNormal dt con tg) ar = mkCTag dt con tg ar
