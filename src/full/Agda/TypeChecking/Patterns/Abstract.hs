{-# LANGUAGE CPP, PatternGuards, ScopedTypeVariables #-}

-- | Tools to manipulate patterns in abstract syntax
--   in the TCM (type checking monad).

module Agda.TypeChecking.Patterns.Abstract where

-- import Control.Applicative
-- import Control.Monad.Error

-- import Data.Maybe (fromMaybe)
-- import Data.Monoid (mempty, mappend)
import Data.List
import Data.Traversable hiding (mapM, sequence)

-- import Agda.Interaction.Options

import Agda.Syntax.Common
import Agda.Syntax.Literal
import Agda.Syntax.Position
import Agda.Syntax.Internal as I
-- import Agda.Syntax.Internal.Pattern
-- import Agda.Syntax.Abstract (IsProjP(..))
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Abstract.Views
import qualified Agda.Syntax.Info as A

import Agda.TypeChecking.Monad
-- import Agda.TypeChecking.Pretty
-- import Agda.TypeChecking.Reduce
-- import Agda.TypeChecking.Substitute
-- import Agda.TypeChecking.Constraints
-- import Agda.TypeChecking.Conversion
-- import Agda.TypeChecking.Datatypes
-- import Agda.TypeChecking.Records
-- import Agda.TypeChecking.Rules.LHS.Problem
import Agda.TypeChecking.Monad.Builtin
-- import Agda.TypeChecking.Free
-- import Agda.TypeChecking.Irrelevance
-- import Agda.TypeChecking.MetaVars

import Agda.Utils.Functor
-- import Agda.Utils.List
-- import Agda.Utils.Maybe
-- import Agda.Utils.Monad
-- import Agda.Utils.Permutation
-- import Agda.Utils.Tuple
-- import qualified Agda.Utils.Pretty as P

#include "../../undefined.h"
import Agda.Utils.Impossible

-- | Expand literal integer pattern into suc/zero constructor patterns.
--
expandLitPattern :: A.NamedArg A.Pattern -> TCM (A.NamedArg A.Pattern)
expandLitPattern p = traverse (traverse expand) p
  where
    expand p = case asView p of
      (xs, A.LitP (LitInt r n))
        | n < 0     -> __IMPOSSIBLE__
        | n > 20    -> tooBig
        | otherwise -> do
          Con z _ <- ignoreSharing <$> primZero
          Con s _ <- ignoreSharing <$> primSuc
          let zero  = A.ConP cinfo (A.AmbQ [setRange r $ conName z]) []
              suc p = A.ConP cinfo (A.AmbQ [setRange r $ conName s]) [defaultNamedArg p]
              info  = A.PatRange r
              cinfo = A.ConPatInfo False info
              p'    = foldr ($) zero $ genericReplicate n suc
          return $ foldr (A.AsP info) p' xs
      _ -> return p
    tooBig = typeError $ GenericError $
      "Matching on natural number literals is done by expanding " ++
      "the literal to the corresponding constructor pattern, so " ++
      "you probably don't want to do it this way."
