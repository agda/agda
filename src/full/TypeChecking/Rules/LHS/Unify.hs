{-# OPTIONS -cpp -fglasgow-exts #-}

module TypeChecking.Rules.LHS.Unify where

import Control.Applicative
import Control.Monad.State
import Control.Monad.Reader

import Data.Map (Map)
import qualified Data.Map as Map

import Syntax.Common
import Syntax.Internal

import TypeChecking.Monad
import TypeChecking.Conversion
import TypeChecking.Constraints
import TypeChecking.Reduce
import TypeChecking.Pretty
import TypeChecking.Substitute
import TypeChecking.Free
import TypeChecking.Records
import TypeChecking.Primitive (constructorForm)

import TypeChecking.Rules.LHS.Problem

#include "../../../undefined.h"

newtype Unify a = U { unUnify :: StateT Sub TCM a }
  deriving (Monad, MonadIO, Functor, Applicative, MonadReader TCEnv)

type Sub = Map Nat Term

instance MonadState TCState Unify where
  get = U $ lift $ get
  put = U . lift . put

instance MonadTCM Unify where
  liftTCM = U . lift

-- | Includes flexible occurrences, metas need to be solved. TODO: relax?
occursCheck :: Nat -> Term -> Type -> Unify ()
occursCheck i u a
  | i `freeIn` u = do
    reportSDoc "tc.lhs.unify" 20 $ prettyTCM (Var i []) <+> text "occurs in" <+> prettyTCM u
    typeError $ UnequalTerms (Var i []) u a
  | otherwise	 = return ()

(|->) :: Nat -> (Term, Type) -> Unify ()
i |-> (u, a) = do
  occursCheck i u a
  reportSDoc "tc.lhs.unify" 15 $ prettyTCM (Var i []) <+> text ":=" <+> prettyTCM u
  U . modify $ Map.insert i u

-- | Compute the unification weak head normal form of a term, i.e. if it's a
-- flexible variable look it up in the current substitution.
ureduce :: Term -> Unify Term
ureduce u = do
  u <- liftTCM $ reduce u
  case u of
    Var i vs -> do
      mv <- U $ gets $ Map.lookup i
      case mv of
	Nothing	-> return u
	Just v	-> ureduce $ v `apply` vs
    _ -> return u

-- | Take a substitution σ and ensure that no variables from the domain appear
--   in the targets. The context of the targets is not changed.
flattenSubstitution :: Substitution -> Substitution
flattenSubstitution s = foldr instantiate s is
  where
    -- instantiated variables
    is = [ i | (i, Just _) <- zip [0..] s ]

    instantiate :: Nat -> Substitution -> Substitution
    instantiate i s = map (fmap $ inst i u) s
      where
	Just u = s !! i

    inst :: Nat -> Term -> Term -> Term
    inst i u v = substs us v
      where us = [var j | j <- [0..i - 1] ] ++ [u] ++ [var j | j <- [i + 1..] ]
	    var j = Var j []

-- | Unify indices.
unifyIndices :: FlexibleVars -> Type -> [Arg Term] -> [Arg Term] -> TCM Substitution
unifyIndices flex a us vs = do
  reportSDoc "tc.lhs.unify" 10 $
    sep [ text "unifyIndices"
	, nest 2 $ text (show flex)
	, nest 2 $ parens (prettyTCM a)
	, nest 2 $ prettyList $ map prettyTCM us
	, nest 2 $ prettyList $ map prettyTCM vs
	, nest 2 $ text "context: " <+> (prettyTCM =<< getContextTelescope)
	]
  s <- flip execStateT Map.empty . unUnify $ unifyArgs a us vs
  let n = maximum $ (-1) : flex
  return $ flattenSubstitution [ Map.lookup i s | i <- [0..n] ]
  where
    flexible i = i `elem` flex

    unifyArgs :: Type -> [Arg Term] -> [Arg Term] -> Unify ()
    unifyArgs _ (_ : _) [] = __IMPOSSIBLE__
    unifyArgs _ [] (_ : _) = __IMPOSSIBLE__
    unifyArgs _ [] [] = return ()
    unifyArgs a us0@(arg@(Arg _ u) : us) vs0@(Arg _ v : vs) = do
      reportSDoc "tc.lhs.unify" 15 $ sep
        [ text "unifyArgs"
	, nest 2 $ parens (prettyTCM a)
	, nest 2 $ prettyList $ map prettyTCM us0
	, nest 2 $ prettyList $ map prettyTCM vs0
        ]
      a <- reduce a
      case funView $ unEl a of
	FunV (Arg _ b) _  -> do
	  unify b u v
	  unifyArgs (a `piApply` [arg]) us vs
	_	  -> __IMPOSSIBLE__

    -- TODO: eta for records here

    unify :: Type -> Term -> Term -> Unify ()
    unify a u v = do
      u <- constructorForm =<< ureduce u
      v <- constructorForm =<< ureduce v
      reportSDoc "tc.lhs.unify" 15 $
	sep [ text "unify"
	    , nest 2 $ parens $ prettyTCM u
	    , nest 2 $ parens $ prettyTCM v
	    , nest 2 $ text ":" <+> prettyTCM a
	    ]
      case (u, v) of
	(Var i us, Var j vs) | i == j  -> do
	    a <- typeOfBV i
	    unifyArgs a us vs
	(Var i [], v) | flexible i -> i |-> (v, a)
	(u, Var j []) | flexible j -> j |-> (u, a)
	(Con c us, Con c' vs) | c == c' -> do
	    -- The type is a datatype or a record.
	    Def d args <- reduce $ unEl a
	    -- Get the number of parameters.
	    def <- theDef <$> getConstInfo d
	    a'  <- case def of
	      Datatype n _ _ _ _ _ -> do
                a <- defType <$> getConstInfo c
                return $ piApply a (take n args)
	      Record n _ _ _ _ _   -> getRecordConstructorType d (take n args)
	      _			   -> __IMPOSSIBLE__
	    unifyArgs a' us vs
	_  -> noConstraints $ equalTerm a u v

