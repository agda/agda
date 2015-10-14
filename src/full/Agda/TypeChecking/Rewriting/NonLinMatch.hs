{-# LANGUAGE CPP                   #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards         #-}
{-# LANGUAGE UndecidableInstances  #-}

{- |  Non-linear matching of the lhs of a rewrite rule against a
      neutral term.

Given a lhs

  Δ ⊢ lhs : B

and a candidate term

  Γ ⊢ t : A

we seek a substitution Γ ⊢ σ : Δ such that

  Γ ⊢ B[σ] = A   and
  Γ ⊢ lhs[σ] = t : A

-}

module Agda.TypeChecking.Rewriting.NonLinMatch where

import Prelude hiding (null, sequence)

import Control.Arrow (first, second)
import Control.Monad.State

import Debug.Trace
import System.IO.Unsafe

import Data.Maybe
import Data.Functor
import Data.Traversable hiding (for)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

import Agda.Syntax.Common
import qualified Agda.Syntax.Common as C
import Agda.Syntax.Internal

import Agda.TypeChecking.EtaContract
import Agda.TypeChecking.Free
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Reduce.Monad
import Agda.TypeChecking.Substitute

import Agda.Utils.Either
import Agda.Utils.Except
import Agda.Utils.Functor
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null

#include "undefined.h"
import Agda.Utils.Impossible

-- | Turn a term into a non-linear pattern, treating the
--   free variables as pattern variables.
--   The first argument is the number of pattern variables.
--   The second argument is the number of bound variables (from pattern lambdas).

class PatternFrom a b where
  patternFrom :: Int -> Int -> a -> TCM b

instance (PatternFrom a b) => PatternFrom [a] [b] where
  patternFrom n k = traverse $ patternFrom n k

instance (PatternFrom a b) => PatternFrom (Arg a) (Arg b) where
  patternFrom n k = traverse $ patternFrom n k

instance (PatternFrom a b) => PatternFrom (Elim' a) (Elim' b) where
  patternFrom n k = traverse $ patternFrom n k

instance (PatternFrom a b) => PatternFrom (Dom a) (Dom b) where
  patternFrom n k = traverse $ patternFrom n k

instance (PatternFrom a b) => PatternFrom (Type' a) (Type' b) where
  patternFrom n k = traverse $ patternFrom n k

instance PatternFrom Term NLPat where
  patternFrom n k v = do
    v <- reduce v
    let done = return $ PTerm v
    case ignoreSharing v of
      Var i es
       | i < k     -> PBoundVar i <$> patternFrom n k es
       | i-k < n,
         null es   -> return $ PVar (i-k)
       | otherwise -> done
      Lam i t  -> PLam i <$> patternFrom n k t
      Lit{}    -> done
      Def f es -> PDef f <$> patternFrom n k es
      Con c vs -> PDef (conName c) <$> patternFrom n k (Apply <$> vs)
      Pi a b   -> PPi <$> patternFrom n k a <*> patternFrom n k b
      Sort{}   -> done
      Level{}  -> return PWild   -- TODO: unLevel and continue
      DontCare{} -> return PWild
      MetaV{}    -> __IMPOSSIBLE__
      Shared{}   -> __IMPOSSIBLE__

instance (PatternFrom a b) => PatternFrom (Abs a) (Abs b) where
  patternFrom n k (Abs name x)   = Abs name   <$> patternFrom n (k+1) x
  patternFrom n k (NoAbs name x) = NoAbs name <$> patternFrom n k x

-- | Monad for non-linear matching.
type NLM = ExceptT Blocked_ (StateT NLMState ReduceM)

type NLMState = (Sub, PostponedEquations)

liftRed :: ReduceM a -> NLM a
liftRed = lift . lift

instance HasOptions NLM where
  pragmaOptions      = liftRed pragmaOptions
  commandLineOptions = liftRed commandLineOptions

runNLM :: NLM () -> ReduceM (Either Blocked_ NLMState)
runNLM nlm = do
  (ok,out) <- runStateT (runExceptT nlm) empty
  case ok of
    Left block -> return $ Left block
    Right _    -> return $ Right out

traceSDocNLM :: VerboseKey -> Int -> TCM Doc -> NLM a -> NLM a
traceSDocNLM k n doc = applyWhenVerboseS k n $ \ cont -> do
  ReduceEnv env st <- liftRed askR
  trace (show $ fst $ unsafePerformIO $ runTCM env st doc) cont

matchingBlocked :: Blocked_ -> NLM ()
matchingBlocked = throwError

-- | Add substitution @i |-> v@ to result of matching.
tellSub :: Int -> Term -> NLM ()
tellSub i v = do
  caseMaybeM (IntMap.lookup i <$> gets fst) (modify $ first $ IntMap.insert i v) $ \v' -> do
    unlessM (liftRed $ equal v v') $ matchingBlocked $ NotBlocked ReallyNotBlocked () -- lies!

tellEq :: Int -> Term -> Term -> NLM ()
tellEq k u v =
  traceSDocNLM "rewriting" 60 (sep
               [ text "adding equality between" <+> prettyTCM u <+> text "(printed in wrong context)"
               , text " and " <+> prettyTCM v
               , text ("(with " ++ show k ++ " free variables)") ]) $ do
  modify $ second $ (PostponedEquation k u v:)

type Sub = IntMap Term

-- | Matching against a term produces a constraint
--   which we have to verify after applying
--   the substitution computed by matching.
data PostponedEquation = PostponedEquation
  { eqFreeVars :: Int -- ^ Number of free variables in the equation
  , eqLhs :: Term     -- ^ Term from pattern, living in pattern context.
  , eqRhs :: Term     -- ^ Term from scrutinee, living in context where matching was invoked.
  }
type PostponedEquations = [PostponedEquation]

-- | Match a non-linear pattern against a neutral term,
--   returning a substitution.

class Match a b where
  match :: Int -> a -> b -> NLM ()

instance Match a b => Match [a] [b] where
  match k ps vs
    | length ps == length vs = zipWithM_ (match k) ps vs
    | otherwise              = matchingBlocked $ NotBlocked ReallyNotBlocked ()

instance Match a b => Match (Arg a) (Arg b) where
  match k p v = match k (unArg p) (unArg v)

instance Match a b => Match (Elim' a) (Elim' b) where
  match k p v =
   case (p, v) of
     (Apply p, Apply v) -> match k p v
     (Proj x , Proj y ) -> if x == y then return () else
                             traceSDocNLM "rewriting" 100 (sep
                               [ text "mismatch between projections " <+> prettyTCM x
                               , text " and " <+> prettyTCM y ]) mzero
     (Apply{}, Proj{} ) -> __IMPOSSIBLE__
     (Proj{} , Apply{}) -> __IMPOSSIBLE__

instance Match a b => Match (Dom a) (Dom b) where
  match k p v = match k (C.unDom p) (C.unDom v)

instance Match a b => Match (Type' a) (Type' b) where
  match k p v = match k (unEl p) (unEl v)

instance (Match a b, Subst t b, Free b, PrettyTCM a, PrettyTCM b) => Match (Abs a) (Abs b) where
  match k (Abs _ p) (Abs _ v) = match (k+1) p v
  match k (Abs _ p) (NoAbs _ v) = match (k+1) p (raise 1 v)
  match k (NoAbs _ p) (Abs _ v) = if (0 `freeIn` v) then no else match k p (raise (-1) v)
    where
      no = traceSDocNLM "rewriting" 100 (sep
        [ text "mismatch between" <+> prettyTCM p
        , text " and " <+> prettyTCM v ]) mzero
  match k (NoAbs _ p) (NoAbs _ v) = match k p v

instance Match NLPat Term where
  match k p v = do
    let yes = return ()
        no  =
          traceSDocNLM "rewriting" 100 (sep
            [ text "mismatch between" <+> prettyTCM p
            , text " and " <+> prettyTCM v]) mzero
    case p of
      PWild  -> yes
      PVar i -> if null (allFreeVars v `IntSet.intersection` IntSet.fromList [0..(k-1)])
                then tellSub i (raise (-k) v)
                else no
      PDef f ps -> do
        v <- liftRed $ constructorForm v
        case ignoreSharing v of
          Def f' es
            | f == f'   -> matchArgs k ps es
            | otherwise -> no
          Con c vs
            | f == conName c -> matchArgs k ps (Apply <$> vs)
            | otherwise -> no
          Lam i u -> do
            let pbody = PDef f (raiseNLP 1 ps ++ [Apply $ Arg i $ PBoundVar 0 []])
            body <- liftRed $ reduce' $ absBody u
            match (k+1) pbody body
          MetaV m es -> do
            matchingBlocked $ Blocked m ()
          _ -> no
      PLam i p' -> do
        let body = Abs (absName p') $ raise 1 v `apply` [Arg i (var 0)]
        body <- liftRed $ reduce' body
        match k p' body
      PPi pa pb  -> case ignoreSharing v of
        Pi a b -> match k pa a >> match k pb b
        _ -> no
      PBoundVar i ps -> case ignoreSharing v of
        Var i' es | i == i' -> matchArgs k ps es
        _ -> no
      PTerm u -> tellEq k u v
    where
      matchArgs :: Int -> [Elim' NLPat] -> Elims -> NLM ()
      matchArgs k ps es = match k ps =<< liftRed (reduce' es)

makeSubstitution :: Sub -> Substitution
makeSubstitution sub
  | IntMap.null sub = idS
  | otherwise       = map val [0 .. highestIndex] ++# idS
  where
    highestIndex = fst $ IntMap.findMax sub  -- find highest key
    val i = fromMaybe (var i) $ IntMap.lookup i sub

checkPostponedEquations :: Substitution -> PostponedEquations -> ReduceM Bool
checkPostponedEquations sub eqs = andM $ for eqs $
  \ (PostponedEquation k lhs rhs) -> equal (applySubst (liftS k sub) lhs) rhs

-- main function
nonLinMatch :: (Match a b) => a -> b -> ReduceM (Either Blocked_ Substitution)
nonLinMatch p v = do
  let no msg b = traceSDoc "rewriting" 100 (sep
                   [ text "matching failed during" <+> text msg
                   , text "blocking: " <+> text (show b) ]) $ return (Left b)
  caseEitherM (runNLM $ match 0 p v) (no "matching") $ \ (s, eqs) -> do
    let sub = makeSubstitution s
    traceSDoc "rewriting" 90 (text $ "sub = " ++ show sub) $ do
      ifM (checkPostponedEquations sub eqs)
        (return $ Right sub)
        (no "checking of postponed equations" $ NotBlocked ReallyNotBlocked ()) -- more lies

-- | Untyped βη-equality, does not handle things like empty record types.
equal :: Term -> Term -> ReduceM Bool
equal u v = do
  (u, v) <- etaContract =<< normalise' (u, v)
  let ok = u == v
  if ok then return True else
    traceSDoc "rewriting" 100 (sep
      [ text "mismatch between " <+> prettyTCM u
      , text " and " <+> prettyTCM v
      ]) $ return False

-- | Raise (bound) variables in a NLPat

class RaiseNLP a where
  raiseNLPFrom :: Int -> Int -> a -> a

  raiseNLP :: Int -> a -> a
  raiseNLP = raiseNLPFrom 0

instance RaiseNLP a => RaiseNLP [a] where
  raiseNLPFrom c k = fmap $ raiseNLPFrom c k

instance RaiseNLP a => RaiseNLP (Arg a) where
  raiseNLPFrom c k = fmap $ raiseNLPFrom c k

instance RaiseNLP a => RaiseNLP (Elim' a) where
  raiseNLPFrom c k = fmap $ raiseNLPFrom c k

instance RaiseNLP a => RaiseNLP (Dom a) where
  raiseNLPFrom c k = fmap $ raiseNLPFrom c k

instance RaiseNLP a => RaiseNLP (Type' a) where
  raiseNLPFrom c k = fmap $ raiseNLPFrom c k

instance RaiseNLP a => RaiseNLP (Abs a) where
  raiseNLPFrom c k (Abs i p)   = Abs i   $ raiseNLPFrom (c+1) k p
  raiseNLPFrom c k (NoAbs i p) = NoAbs i $ raiseNLPFrom c     k p

instance RaiseNLP NLPat where
  raiseNLPFrom c k p = case p of
    PVar _ -> p
    PWild  -> p
    PDef f ps -> PDef f $ raiseNLPFrom c k ps
    PLam i q -> PLam i $ raiseNLPFrom c k q
    PPi a b -> PPi (raiseNLPFrom c k a) (raiseNLPFrom c k b)
    PBoundVar i ps -> let j = if i < c then i else i + k
                      in PBoundVar j $ raiseNLPFrom c k ps
    PTerm u -> PTerm $ raiseFrom c k u

