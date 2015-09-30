{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Tools to manipulate patterns in abstract syntax
--   in the TCM (type checking monad).

module Agda.TypeChecking.Patterns.Abstract where

import Data.List
import Data.Traversable hiding (mapM, sequence)
import Data.Void

import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Abstract.Views
import Agda.Syntax.Concrete (FieldAssignment')
import Agda.Syntax.Common
import Agda.Syntax.Info as A
import Agda.Syntax.Internal as I
import Agda.Syntax.Literal
import Agda.Syntax.Position

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin

import Agda.Utils.Functor

#include "undefined.h"
import Agda.Utils.Impossible

-- | Expand literal integer pattern into suc/zero constructor patterns.
--
expandLitPattern :: NamedArg A.Pattern -> TCM (NamedArg A.Pattern)
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
              cinfo = A.ConPatInfo ConPCon info
              p'    = foldr ($) zero $ genericReplicate n suc
          return $ foldr (A.AsP info) p' xs
      _ -> return p
    tooBig = typeError $ GenericError $
      "Matching on natural number literals is done by expanding " ++
      "the literal to the corresponding constructor pattern, so " ++
      "you probably don't want to do it this way."


-- | Expand away (deeply) all pattern synonyms in a pattern.
class ExpandPatternSynonyms a where
  expandPatternSynonyms :: a -> TCM a

instance ExpandPatternSynonyms a => ExpandPatternSynonyms (Maybe a) where
  expandPatternSynonyms = traverse expandPatternSynonyms

instance ExpandPatternSynonyms a => ExpandPatternSynonyms [a] where
  expandPatternSynonyms = traverse expandPatternSynonyms

instance ExpandPatternSynonyms a => ExpandPatternSynonyms (Arg a) where
  expandPatternSynonyms = traverse expandPatternSynonyms

instance ExpandPatternSynonyms a => ExpandPatternSynonyms (Named n a) where
  expandPatternSynonyms = traverse expandPatternSynonyms

instance ExpandPatternSynonyms a => ExpandPatternSynonyms (FieldAssignment' a) where
  expandPatternSynonyms = traverse expandPatternSynonyms

instance ExpandPatternSynonyms A.Pattern where
 expandPatternSynonyms p =
  case p of
    A.VarP{}             -> return p
    A.WildP{}            -> return p
    A.DotP{}             -> return p
    A.LitP{}             -> return p
    A.AbsurdP{}          -> return p
    A.ConP i ds as       -> A.ConP i ds <$> expandPatternSynonyms as
    A.DefP i q as        -> A.DefP i q <$> expandPatternSynonyms as
    A.AsP i x p          -> A.AsP i x <$> expandPatternSynonyms p
    A.RecP i as          -> A.RecP i <$> expandPatternSynonyms as
    A.PatternSynP i x as -> setCurrentRange i $ do
      p <- killRange <$> lookupPatternSyn x
        -- Must expand arguments before instantiating otherwise pattern
        -- synonyms could get into dot patterns (which is __IMPOSSIBLE__)
      instPatternSyn p =<< expandPatternSynonyms as

      where
        instPatternSyn :: A.PatternSynDefn -> [NamedArg A.Pattern] -> TCM A.Pattern
        instPatternSyn (ns, p) as = do
          p <- expandPatternSynonyms (vacuous p)
          case A.insertImplicitPatSynArgs (A.WildP . PatRange) (getRange x) ns as of
            Nothing       -> typeError $ BadArgumentsToPatternSynonym x
            Just (_, _:_) -> typeError $ TooFewArgumentsToPatternSynonym x
            Just (s, [])  -> return $ setRange (getRange i) $ A.substPattern s p
