{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE CPP, DeriveDataTypeable #-}
-- | Defines UHC Core functions used in other parts of Agda.
-- E.g. parsing Core pragmas uses the `parseCoreCode` function.
module Agda.Compiler.UHC.Pragmas.Base
  ( CoreExpr,
    CoreTypeName,
    CoreType (..),
    CoreConstr (..),
    coreConstrToCTag,
    setTag,
    HsName
  )
where


import Data.Typeable

import Agda.Compiler.UHC.AuxAST
import Agda.Compiler.UHC.Bridge as CA

#include "undefined.h"
import Agda.Utils.Impossible


type CoreTypeName = Maybe HsName -- nothing for unit, else the name.

-- if it is a magic type, then the name of the magic dataype.
data CoreType
  = CTMagic CoreTypeName String -- Magic name
  | CTNormal CoreTypeName
  deriving (Eq, Show, Typeable)

type CoreExpr = CExpr

-- We need an explicit representation for constructors, as we need to serialise the CoreConstr
-- to store it inside agdai files. Else we could just use a partially applied
-- CTag constructor instead (we don't know the arity yet...).
data CoreConstr
  = CCMagic CTag -- special well-known type with fixed arity (e.g. Bool, List, etc.)
  | CCNormal HsName HsName Int -- datatype, constr, tag
  deriving (Eq, Show, Typeable)


setTag :: CoreConstr -> Int -> CoreConstr
setTag (CCNormal a b _) t = CCNormal a b t
setTag _ _ = __IMPOSSIBLE__

coreConstrToCTag :: CoreConstr
    -> Int -- ^ Arity
    -> CTag
coreConstrToCTag (CCMagic ctg) _ = ctg
coreConstrToCTag (CCNormal dt con tg) ar = mkCTag dt con tg ar

