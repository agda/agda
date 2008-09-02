
module Agda.TypeChecking.SizedTypes where

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import {-# SOURCE #-} Agda.TypeChecking.Conversion

compareSizes :: MonadTCM tcm => Comparison -> Term -> Term -> tcm Constraints
compareSizes cmp u v = do
  reportSDoc "tc.conv.size" 10 $ vcat
    [ text "Comparing sizes"
    , nest 2 $ sep [ prettyTCM u <+> prettyTCM cmp
                   , prettyTCM v
                   ]
    ]
  s1   <- sizeView =<< reduce u
  s2   <- sizeView =<< reduce v
  size <- sizeType
  case (cmp, s1, s2) of
    (CmpLeq, _,         SizeInf)   -> return []
    (CmpEq,  SizeSuc u, SizeInf)   -> compareSizes CmpEq u v
    (_,      SizeInf,   SizeSuc v) -> compareSizes CmpEq u v
    _                              -> compareAtom cmp size u v

