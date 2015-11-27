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

#if __GLASGOW_HASKELL__ <= 708
import Data.Foldable ( foldMap )
#endif

import Data.Maybe
import Data.Functor
import Data.Traversable hiding (for)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.List (elemIndex)

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
import Agda.Utils.Singleton
import Agda.Utils.Size

#include "undefined.h"
import Agda.Utils.Impossible

-- | Turn a term into a non-linear pattern, treating the
--   free variables as pattern variables.
--   The first argument is the number of bound variables (from pattern lambdas).

class PatternFrom a b where
  patternFrom :: Int -> a -> TCM b

instance (PatternFrom a b) => PatternFrom [a] [b] where
  patternFrom k = traverse $ patternFrom k

instance (PatternFrom a b) => PatternFrom (Arg a) (Arg b) where
  patternFrom k = traverse $ patternFrom k

instance (PatternFrom a b) => PatternFrom (Elim' a) (Elim' b) where
  patternFrom k = traverse $ patternFrom k

instance (PatternFrom a b) => PatternFrom (Dom a) (Dom b) where
  patternFrom k = traverse $ patternFrom k

instance (PatternFrom a b) => PatternFrom (Type' a) (Type' b) where
  patternFrom k = traverse $ patternFrom k

instance PatternFrom Term NLPat where
  patternFrom k v = do
    v <- reduce v
    let done = return $ PTerm v
    case ignoreSharing v of
      Var i es
       | i < k     -> PBoundVar i <$> patternFrom k es
       | null es   -> do
           let i' = i-k
           -- Pattern variables are labeled with their context id, because they
           -- can only be instantiated once they're no longer bound by the
           -- context (see Issue 1652).
           id <- (!! i') <$> getContextId
           return $ PVar (Just id) i'
       | otherwise -> done
      Lam i t  -> PLam i <$> patternFrom k t
      Lit{}    -> done
      Def f es -> PDef f <$> patternFrom k es
      Con c vs -> PDef (conName c) <$> patternFrom k (Apply <$> vs)
      Pi a b   -> PPi <$> patternFrom k a <*> patternFrom k b
      Sort{}   -> done
      Level{}  -> return PWild   -- TODO: unLevel and continue
      DontCare{} -> return PWild
      MetaV{}    -> __IMPOSSIBLE__
      Shared{}   -> __IMPOSSIBLE__

instance (PatternFrom a b) => PatternFrom (Abs a) (Abs b) where
  patternFrom k (Abs name x)   = Abs name   <$> patternFrom (k+1) x
  patternFrom k (NoAbs name x) = NoAbs name <$> patternFrom k x

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

tellEq :: Telescope -> Telescope -> Term -> Term -> NLM ()
tellEq gamma k u v =
  traceSDocNLM "rewriting" 60 (sep
               [ text "adding equality between" <+> addContext (gamma `abstract` k) (prettyTCM u)
               , text " and " <+> addContext k (prettyTCM v) ]) $ do
  modify $ second $ (PostponedEquation k u v:)

type Sub = IntMap Term

-- | Matching against a term produces a constraint
--   which we have to verify after applying
--   the substitution computed by matching.
data PostponedEquation = PostponedEquation
  { eqFreeVars :: Telescope -- ^ Telescope of free variables in the equation
  , eqLhs :: Term     -- ^ Term from pattern, living in pattern context.
  , eqRhs :: Term     -- ^ Term from scrutinee, living in context where matching was invoked.
  }
type PostponedEquations = [PostponedEquation]

-- | Match a non-linear pattern against a neutral term,
--   returning a substitution.

class Match a b where
  match :: Telescope  -- ^ The telescope of pattern variables
        -> Telescope  -- ^ The telescope of lambda-bound variables
        -> a          -- ^ The pattern to match
        -> b          -- ^ The term to be matched against the pattern
        -> NLM ()

instance Match a b => Match [a] [b] where
  match gamma k ps vs
    | length ps == length vs = zipWithM_ (match gamma k) ps vs
    | otherwise              = matchingBlocked $ NotBlocked ReallyNotBlocked ()

instance Match a b => Match (Arg a) (Arg b) where
  match gamma k p v = match gamma k (unArg p) (unArg v)

instance Match a b => Match (Elim' a) (Elim' b) where
  match gamma k p v =
   case (p, v) of
     (Apply p, Apply v) -> match gamma k p v
     (Proj x , Proj y ) -> if x == y then return () else
                             traceSDocNLM "rewriting" 80 (sep
                               [ text "mismatch between projections " <+> prettyTCM x
                               , text " and " <+> prettyTCM y ]) mzero
     (Apply{}, Proj{} ) -> __IMPOSSIBLE__
     (Proj{} , Apply{}) -> __IMPOSSIBLE__

instance Match a b => Match (Dom a) (Dom b) where
  match gamma k p v = match gamma k (C.unDom p) (C.unDom v)

instance Match a b => Match (Type' a) (Type' b) where
  match gamma k p v = match gamma k (unEl p) (unEl v)

instance (Match a b, Subst t1 a, Subst t2 b, PrettyTCM a, PrettyTCM b) => Match (Abs a) (Abs b) where
  match gamma k (Abs n p) (Abs _ v) = match gamma (ExtendTel dummyDom (Abs n k)) p v
  match gamma k (Abs n p) (NoAbs _ v) = match gamma (ExtendTel dummyDom (Abs n k)) p (raise 1 v)
  match gamma k (NoAbs n p) (Abs _ v) = match gamma (ExtendTel dummyDom (Abs n k)) (raise 1 p) v
  match gamma k (NoAbs _ p) (NoAbs _ v) = match gamma k p v

instance Match NLPat Term where
  match gamma k p v = do
    let n = size k
    traceSDocNLM "rewriting" 100 (sep
      [ text "matching" <+> addContext (gamma `abstract` k) (prettyTCM (raisePatVars n p))
      , text "with" <+> addContext k (prettyTCM v)]) $ do
    let yes = return ()
        no msg =
          traceSDocNLM "rewriting" 80 (sep
            [ text "mismatch between" <+> addContext (gamma `abstract` k) (prettyTCM (raisePatVars n p))
            , text " and " <+> addContext k (prettyTCM v)
            , msg ]) mzero
    case p of
      PWild  -> yes
      PVar id i -> do
        -- If the variable is still bound by the current context, we cannot
        -- instantiate it so it has to match on the nose (see Issue 1652).
        ctx <- zip <$> getContextNames <*> getContextId
        traceSDocNLM "rewriting" 90 (text "Current context:" <+> (prettyTCM ctx)) $ do
        cid <- getContextId
        case (maybe Nothing (\i -> elemIndex i cid) id) of
          Just j -> if v == var (j+n)
                    then tellSub i (var j)
                    else no (text $ "(CtxId = " ++ show id ++ ")")
          Nothing -> do
            let boundVarOccs :: FreeVars
                boundVarOccs = runFree (\var@(i,_) -> if i < n then singleton var else empty) IgnoreNot v
            if null (rigidVars boundVarOccs)
               then if null (flexibleVars boundVarOccs)
                    then tellSub i (raise (-n) v)
                    else matchingBlocked $ foldMap (foldMap $ \m -> Blocked m ()) $ flexibleVars boundVarOccs
               else no (text "")
      PDef f ps -> do
        v <- liftRed $ constructorForm v
        case ignoreSharing v of
          Def f' es
            | f == f'   -> matchArgs gamma k ps es
            | otherwise -> no (text "")
          Con c vs
            | f == conName c -> matchArgs gamma k ps (Apply <$> vs)
            | otherwise -> no (text "")
          Lam i u -> do
            let pbody = PDef f (raiseNLP 1 ps ++ [Apply $ Arg i $ PBoundVar 0 []])
            body <- liftRed $ reduce' $ absBody u
            match gamma (ExtendTel dummyDom (Abs (absName u) k)) pbody body
          MetaV m es -> do
            matchingBlocked $ Blocked m ()
          _ -> no (text "")
      PLam i p' -> do
        let body = Abs (absName p') $ raise 1 v `apply` [Arg i (var 0)]
        body <- liftRed $ reduce' body
        match gamma k p' body
      PPi pa pb  -> case ignoreSharing v of
        Pi a b -> do
          (a,b) <- liftRed $ reduce' (a,b)
          match gamma k pa a >> match gamma k pb b
        MetaV m es -> matchingBlocked $ Blocked m ()
        _ -> no (text "")
      PBoundVar i ps -> case ignoreSharing v of
        Var i' es | i == i' -> matchArgs gamma k ps es
        MetaV m es -> matchingBlocked $ Blocked m ()
        _ -> no (text "")
      PTerm u -> tellEq gamma k u v
    where
      matchArgs :: Telescope -> Telescope -> [Elim' NLPat] -> Elims -> NLM ()
      matchArgs gamma k ps es = match gamma k ps =<< liftRed (reduce' es)

makeSubstitution :: Telescope -> Sub -> Substitution
makeSubstitution gamma sub =
  prependS __IMPOSSIBLE__ (map val [0 .. size gamma-1]) EmptyS
    where
      val i = IntMap.lookup i sub

checkPostponedEquations :: Substitution -> PostponedEquations -> ReduceM Bool
checkPostponedEquations sub eqs = andM $ for eqs $
  \ (PostponedEquation k lhs rhs) -> equal (applySubst (liftS (size k) sub) lhs) rhs

-- main function
nonLinMatch :: (Match a b) => Telescope -> a -> b -> ReduceM (Either Blocked_ Substitution)
nonLinMatch gamma p v = do
  let no msg b = traceSDoc "rewriting" 80 (sep
                   [ text "matching failed during" <+> text msg
                   , text "blocking: " <+> text (show b) ]) $ return (Left b)
  caseEitherM (runNLM $ match gamma EmptyTel p v) (no "matching") $ \ (s, eqs) -> do
    let sub = makeSubstitution gamma s
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
    traceSDoc "rewriting" 80 (sep
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
    PVar _ _ -> p
    PWild  -> p
    PDef f ps -> PDef f $ raiseNLPFrom c k ps
    PLam i q -> PLam i $ raiseNLPFrom c k q
    PPi a b -> PPi (raiseNLPFrom c k a) (raiseNLPFrom c k b)
    PBoundVar i ps -> let j = if i < c then i else i + k
                      in PBoundVar j $ raiseNLPFrom c k ps
    PTerm u -> PTerm $ raiseFrom c k u

