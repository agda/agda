{-# LANGUAGE CPP                        #-}
{-# LANGUAGE TypeFamilies               #-}

module Agda.TypeChecking.Heterogeneous.Instances where

import Data.Semigroup ((<>))

import Agda.TypeChecking.Heterogeneous

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Free.Lazy (Free(..), underBinder)
import Agda.TypeChecking.MetaVars.Mention
import Agda.TypeChecking.Monad.Constraints (isProblemSolved)
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Monad.Context (MonadAddContext(..), AddContext(..))

import Agda.Syntax.Internal as I
import Agda.Syntax.Internal.Generic (TermLike(..))

import Agda.Utils.Monad (allM)

import Agda.Utils.Impossible

---------------------------------------------------------------------
-- Agda.TypeChecking.Free.Lazy
---------------------------------------------------------------------

instance Free ContextHet where
  freeVars' = go
    where
      go Empty      = mempty
      go (v :⊢: vs) = freeVars' v <> underBinder (freeVars' vs)

---------------------------------------------------------------------
-- Instances for Agda.TypeChecking.MetaVars.Mention
---------------------------------------------------------------------
------------------------------------------------------------------
-- Instances for Agda.TypeChecking.Reduce
------------------------------------------------------------------
---------------------------------------------------------------------
-- Agda.Syntax.Internal.Generic
---------------------------------------------------------------------

instance TermLike ContextHet where
  foldTerm f = foldTerm f . contextHetToList
  traverseTermM = __IMPOSSIBLE__

---------------------------------------------------------------------
-- Agda.Utils.Size
---------------------------------------------------------------------

