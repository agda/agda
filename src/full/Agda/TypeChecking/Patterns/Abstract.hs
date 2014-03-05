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
import Agda.Syntax.Info as A

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


-- | Expand away (deeply) all pattern synonyms in a pattern.
--
expandPatternSynonyms :: A.Pattern -> TCM A.Pattern
expandPatternSynonyms p =
  case p of
    A.VarP{}             -> return p
    A.WildP{}            -> return p
    A.DotP{}             -> return p
    A.ImplicitP{}        -> return p
    A.LitP{}             -> return p
    A.AbsurdP{}          -> return p
    A.ConP i ds as       -> A.ConP i ds <$> (traverse . traverse . traverse) expandPatternSynonyms as
    A.DefP i q as        -> A.DefP i q <$> (traverse . traverse . traverse) expandPatternSynonyms as
    A.AsP i x p          -> A.AsP i x <$> expandPatternSynonyms p
    A.PatternSynP i x as ->
      setCurrentRange (getRange i) $ do
        p <- killRange <$> lookupPatternSyn x
                             -- Must expand arguments before instantiating otherwise pattern
                             -- synonyms could get into dot patterns (which is __IMPOSSIBLE__)
        instPatternSyn p =<< (traverse . traverse . traverse) expandPatternSynonyms as
      where
        instPatternSyn :: A.PatternSynDefn -> [A.NamedArg A.Pattern] -> TCM A.Pattern
        instPatternSyn (ns, p) as = do
          p <- expandPatternSynonyms p
          case A.insertImplicitPatSynArgs (A.ImplicitP . PatRange) (getRange x) ns as of
            Nothing       -> typeError $ GenericError $ "Bad arguments to pattern synonym " ++ show x
            Just (_, _:_) -> typeError $ GenericError $ "Too few arguments to pattern synonym " ++ show x
            Just (s, [])  -> return $ setRange (getRange i) $ A.substPattern s p
