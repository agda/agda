{-# LANGUAGE CPP          #-}
{-# LANGUAGE TypeFamilies #-}

-- | Tools to manipulate patterns in abstract syntax
--   in the TCM (type checking monad).

module Agda.TypeChecking.Patterns.Abstract where

import Data.List
import Data.Traversable hiding (mapM, sequence)
import Data.Void

import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Abstract.Pattern
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
      (xs, A.LitP (LitNat r n))
        | n < 0     -> negLit -- Andreas, issue #2365, negative literals not yet supported.
        | n > 20    -> tooBig
        | otherwise -> do
          Con z _ _ <- ignoreSharing <$> primZero
          Con s _ _ <- ignoreSharing <$> primSuc
          let zero  = A.ConP cinfo (A.AmbQ [setRange r $ conName z]) []
              suc p = A.ConP cinfo (A.AmbQ [setRange r $ conName s]) [defaultNamedArg p]
              info  = A.PatRange r
              cinfo = A.ConPatInfo ConOCon info
              p'    = foldr ($) zero $ genericReplicate n suc
          return $ foldr (A.AsP info) p' xs
      _ -> return p
    tooBig = typeError $ GenericError $
      "Matching on natural number literals is done by expanding " ++
      "the literal to the corresponding constructor pattern, so " ++
      "you probably don't want to do it this way."
    negLit = typeError $ GenericError $
      "Negative literals are not supported in patterns"


-- | Expand away (deeply) all pattern synonyms in a pattern.

-- Unfortunately, the more general type signature
--
--   expandPatternSynonyms :: forall a p . APatternLike a p => p -> TCM p
--
-- is rejected by GHC 7.10
--
--   Could not deduce (APatternLike A.Expr p)
--     arising from a use of ‘postTraverseAPatternM’
--
-- I am mystified (Andreas, 2017-07-27)

-- expandPatternSynonyms :: forall a p . APatternLike a p => p -> TCM p

-- As a workaround, we define this function only for a = A.Exp, p = A.Pattern'
-- and keep the type class ExpandPatternSynonyms (which would otherwise be superfluous).

expandPatternSynonyms' :: A.Pattern -> TCM A.Pattern
expandPatternSynonyms' = postTraverseAPatternM $ \case

  A.PatternSynP i x as -> setCurrentRange i $ do
    (ns, p) <- killRange <$> lookupPatternSyn x

    -- Must expand arguments before instantiating otherwise pattern
    -- synonyms could get into dot patterns (which is __IMPOSSIBLE__).
    p :: A.Pattern <- expandPatternSynonyms' (vacuous p :: A.Pattern)

    case A.insertImplicitPatSynArgs (A.WildP . PatRange) (getRange x) ns as of
      Nothing       -> typeError $ BadArgumentsToPatternSynonym x
      Just (_, _:_) -> typeError $ TooFewArgumentsToPatternSynonym x
      Just (s, [])  -> return $ setRange (getRange i) $ A.substPattern s p

  p -> return p

class ExpandPatternSynonyms a where
  expandPatternSynonyms :: a -> TCM a

  default expandPatternSynonyms
    :: (Traversable f, ExpandPatternSynonyms b, f b ~ a) => a -> TCM a
  expandPatternSynonyms = traverse expandPatternSynonyms

instance ExpandPatternSynonyms a => ExpandPatternSynonyms (Maybe a)            where
instance ExpandPatternSynonyms a => ExpandPatternSynonyms [a]                  where
instance ExpandPatternSynonyms a => ExpandPatternSynonyms (Arg a)              where
instance ExpandPatternSynonyms a => ExpandPatternSynonyms (Named n a)          where
instance ExpandPatternSynonyms a => ExpandPatternSynonyms (FieldAssignment' a) where

instance ExpandPatternSynonyms A.Pattern where
  expandPatternSynonyms = expandPatternSynonyms'
