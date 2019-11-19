{-# LANGUAGE GADTs #-}

-- | Tools to manipulate patterns in internal syntax
--   in the TCM (type checking monad).

module Agda.TypeChecking.Patterns.Internal where

import Control.Monad

import Data.Maybe

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Reduce (reduce)
import Agda.TypeChecking.Substitute.DeBruijn

import Agda.Utils.Impossible

-- | Convert a term (from a dot pattern) to a DeBruijn pattern.

class TermToPattern a b where
  termToPattern :: a -> TCM b

  default termToPattern :: (TermToPattern a' b', Traversable f, a ~ f a', b ~ f b') => a -> TCM b
  termToPattern = traverse termToPattern

instance TermToPattern a b => TermToPattern [a] [b] where
instance TermToPattern a b => TermToPattern (Arg a) (Arg b) where
instance TermToPattern a b => TermToPattern (Named c a) (Named c b) where

instance (DeBruijn (Pattern' a)) => TermToPattern Term (Pattern' a) where
  termToPattern t = (reduce >=> constructorForm) t >>= \case
    -- Constructors.
    Con c _ args -> ConP c noConPatternInfo . map (fmap unnamed) <$> termToPattern (fromMaybe __IMPOSSIBLE__ $ allApplyElims args)
    Var i []    -> return $ deBruijnVar i
    Lit l       -> return $ litP l
    t           -> return $ dotP t

dotPatternsToPatterns :: forall a. (DeBruijn (Pattern' a))
                      => Pattern' a -> TCM (Pattern' a)
dotPatternsToPatterns = postTraversePatternM dotToPat
  where
    dotToPat :: Pattern' a -> TCM (Pattern' a)
    dotToPat = \case
      DotP o t -> termToPattern t
      p        -> return p
