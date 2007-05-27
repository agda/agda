{-# OPTIONS -cpp #-}

module TypeChecking.Rules.LHS.Split where

import Control.Applicative
import Control.Monad.Error
import Data.Monoid

import Syntax.Common
import Syntax.Literal
import Syntax.Position
import Syntax.Internal
import Syntax.Internal.Pattern
import qualified Syntax.Abstract as A

import TypeChecking.Monad
import TypeChecking.Pretty
import TypeChecking.Reduce
import TypeChecking.Constraints
import TypeChecking.Conversion
import TypeChecking.Rules.LHS.Problem
import TypeChecking.Rules.Term

import Utils.Permutation
import Utils.Tuple

#include "../../../undefined.h"

instance (Monad m, Error err) => Applicative (ErrorT err m) where
  pure	= return
  (<*>) = ap

instance (Error err, MonadTCM tcm) => MonadTCM (ErrorT err tcm) where
  liftTCM = lift . liftTCM

-- | TODO: move to Syntax.Abstract.View
asView :: A.Pattern -> ([Name], A.Pattern)
asView (A.AsP _ x p) = (x :) -*- id $ asView p
asView p	     = ([], p)

-- | Split a problem at the first constructor of datatype type. Implicit
--   patterns should have been inserted.
splitProblem :: Problem -> TCM (Either SplitError SplitProblem)
splitProblem (Problem ps (perm, qs) tel) = runErrorT $
    splitP ps (permute perm $ zip [0..] $ allHoles qs) tel
  where
    splitP :: [NamedArg A.Pattern] -> [(Int, OneHolePatterns)] -> Telescope -> ErrorT SplitError TCM SplitProblem
    splitP _	    []		 (ExtendTel _ _)	 = __IMPOSSIBLE__
    splitP _	    (_:_)	  EmptyTel		 = __IMPOSSIBLE__
    splitP []	     _		  _			 = throwError $ NothingToSplit
    splitP ps	    []		  EmptyTel		 = __IMPOSSIBLE__
    splitP (p : ps) ((i, q) : qs) tel0@(ExtendTel a tel) =
      case asView $ namedThing $ unArg p of
	(xs, A.LitP lit)  -> do
	  b <- lift $ litType lit
	  ok <- lift $ do
	      noConstraints (equalType (unArg a) b)
	      return True
	    `catchError` \_ -> return False
	  if ok
	    then return $
	      Split mempty
		    xs
		    (fmap (LitFocus lit q i) a)
		    (fmap (Problem ps ()) tel)
	    else keepGoing
	(xs, A.ConP _ c args) -> do
	  a' <- reduce $ unArg a
	  case unEl a' of
	    Def d vs	-> do
	      def <- theDef <$> getConstInfo d
	      case def of
		Datatype np _ _ _ _ _ -> do
		  let (pars, ixs) = splitAt np vs
		  reportSDoc "tc.lhs.split" 10 $
		    vcat [ sep [ text "splitting on"
			       , nest 2 $ fsep [ prettyA p, text ":", prettyTCM a ]
			       ]
			 , nest 2 $ text "pars =" <+> fsep (punctuate comma $ map prettyTCM pars)
			 , nest 2 $ text "ixs  =" <+> fsep (punctuate comma $ map prettyTCM ixs)
			 ]
		  return $ Split mempty
				 xs
				 (fmap (const $ Focus c args (getRange p) q i d pars ixs) a)
				 (fmap (Problem ps ()) tel)
		-- TODO: record patterns
		_ -> keepGoing
	    _	-> keepGoing
	p -> keepGoing
      where
	keepGoing = do
	  let p0 = Problem [p] () (ExtendTel a $ fmap (const EmptyTel) tel)
	  Split p1 xs foc p2 <- underAbstraction a tel $ \tel -> splitP ps qs tel
	  return $ Split (mappend p0 p1) xs foc p2


