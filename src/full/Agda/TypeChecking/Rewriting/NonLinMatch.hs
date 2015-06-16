-- GHC 7.4.2 requires this layout for the pragmas. See Issue 1460.
{-# LANGUAGE CPP,
             FlexibleInstances,
             MultiParamTypeClasses #-}

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

import Prelude hiding (sequence)

import Control.Monad.Trans.Maybe
import Control.Monad.Writer hiding (forM, sequence)

import Debug.Trace
import System.IO.Unsafe

import Data.Maybe
import Data.Functor
import Data.Traversable hiding (for)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap

import Agda.Syntax.Common (unArg)
import Agda.Syntax.Internal

import Agda.TypeChecking.EtaContract
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
import Agda.Utils.Singleton

#include "undefined.h"
import Agda.Utils.Impossible

-- nonLinMatch :: NLPat -> Term -> ReduceM (Maybe Substitution)
-- nonLinMatch p v = do
--   let no = return Nothing
--   caseMaybeM (execNLM $ ambMatch p v) no $ \ (sub, eqs) -> do
--     -- Check that the substitution is non-ambiguous and total.
--     msub <- runWriterT $ Map.forM sub $ \case
--       [v] -> return v
--       []  -> mzero
--       (v : vs) -> v <$ forM_ vs $ \ u -> do
--         ifM (equal v u) (return ()) mzero
--     caseMaybe msub no $ \ sub' -> do
--     --
--     -- Check that the equations are satisfied.

-- -- | Non-linear (non-constructor) first-order pattern.
-- data NLPat
--   = PVar {-# UNPACK #-} !Int
--     -- ^ Matches anything (modulo non-linearity).
--   | PWild
--     -- ^ Matches anything (e.g. irrelevant terms).
--   | PDef QName PElims
--     -- ^ Matches @f es@
--   | PTerm Term
--     -- ^ Matches the term modulo β (ideally βη).
-- type PElims = [Elim' NLPat]

-- | Turn a term into a non-linear pattern, treating the
--   free variables as pattern variables.

class PatternFrom a b where
  patternFrom :: a -> TCM b

instance (Traversable f, PatternFrom a b) => PatternFrom (f a) (f b) where
  patternFrom = traverse patternFrom

instance PatternFrom Term NLPat where
  patternFrom v = do
    v <- etaContract =<< reduce v
    let done = return $ PTerm v
    case ignoreSharing v of
      Var i [] -> return $ PVar i
      Var{}    -> done
      Lam{}    -> done
      Lit{}    -> done
      Def f es -> PDef f <$> patternFrom es
      Con c vs -> PDef (conName c) <$> patternFrom (Apply <$> vs)
      Pi{}     -> done
      Sort{}   -> done
      Level{}  -> return PWild   -- TODO: unLevel and continue
      DontCare{} -> return PWild
      MetaV{}    -> __IMPOSSIBLE__
      Shared{}   -> __IMPOSSIBLE__


-- | Monad for non-linear matching.
type NLM = ExceptT Blocked_ (WriterT NLMOut ReduceM)

type NLMOut = (AmbSubst, PostponedEquations)

liftRed :: ReduceM a -> NLM a
liftRed = lift . lift

instance HasOptions NLM where
  pragmaOptions      = liftRed pragmaOptions
  commandLineOptions = liftRed commandLineOptions

runNLM :: NLM () -> ReduceM (Either Blocked_ NLMOut)
runNLM nlm = do
  (ok,out) <- runWriterT $ runExceptT nlm
  case ok of
    Left block -> return $ Left block
    Right _    -> return $ Right out

traceSDocNLM :: VerboseKey -> Int -> TCM Doc -> NLM a -> NLM a
traceSDocNLM k n doc = applyWhenVerboseS k n $ \ cont -> do
  ReduceEnv env st <- liftRed askR
  trace (show $ fst $ unsafePerformIO $ runTCM env st doc) cont

-- execNLM :: NLM a -> ReduceM (Maybe NLMOut)
-- execNLM m = runMaybeT $ execWriterT m

matchingBlocked :: Blocked_ -> NLM ()
matchingBlocked = throwError

-- | Add substitution @i |-> v@ to result of matching.
tellSubst :: Int -> Term -> NLM ()
tellSubst i v = tell (singleton (i, v), mempty)

tellEq :: Term -> Term -> NLM ()
tellEq u v = traceSDocNLM "rewriting" 60 (sep
               [ text "adding equality between" <+> prettyTCM u
               , text " and " <+> prettyTCM v]) $ tell (mempty, singleton $ PostponedEquation u v)

-- | Non-linear matching returns first an ambiguous substitution,
--   mapping one de Bruijn index to possibly several terms.
newtype AmbSubst = AmbSubst { ambSubst :: IntMap [Term] }

instance Monoid AmbSubst where
  mempty                          = AmbSubst mempty
  AmbSubst m `mappend` AmbSubst n = AmbSubst $ IntMap.unionWith (++) m n

instance Singleton (Int,Term) AmbSubst where
  singleton (i, v) = AmbSubst $ IntMap.singleton i [v]

-- sgSubst :: Int -> Term -> AmbSubst
-- sgSubst i v = AmbSubst $ IntMap.singleton i [v]

-- | Matching against a term produces a constraint
--   which we have to verify after applying
--   the substitution computed by matching.
data PostponedEquation = PostponedEquation
  { eqLhs :: Term  -- ^ Term from pattern, living in pattern context.
  , eqRhs :: Term  -- ^ Term from scrutinee, living in context where matching was invoked.
  }
type PostponedEquations = [PostponedEquation]

-- | Match a non-linear pattern against a neutral term,
--   returning a substitution.

class AmbMatch a b where
  ambMatch :: a -> b -> NLM ()

instance AmbMatch a b => AmbMatch [a] [b] where
  ambMatch ps vs
    | length ps == length vs = zipWithM_ ambMatch ps vs
    | length ps >  length vs = do
        matchingBlocked $ NotBlocked (Underapplied) ()
    | otherwise              = __IMPOSSIBLE__

instance AmbMatch a b => AmbMatch (Arg a) (Arg b) where
  ambMatch p v = ambMatch (unArg p) (unArg v)

instance AmbMatch a b => AmbMatch (Elim' a) (Elim' b) where
  ambMatch p v =
   case (p, v) of
     (Apply p, Apply v) -> ambMatch p v
     (Proj x , Proj y ) -> if x == y then return () else
                             traceSDocNLM "rewriting" 100 (sep
                               [ text "mismatch between projections " <+> prettyTCM x
                               , text " and " <+> prettyTCM y ]) mzero
     (Apply{}, Proj{} ) -> __IMPOSSIBLE__
     (Proj{} , Apply{}) -> __IMPOSSIBLE__

instance AmbMatch NLPat Term where
  ambMatch p v = do
    let yes = return ()
        no x y =
          traceSDocNLM "rewriting" 100 (sep
            [ text "mismatch between" <+> prettyTCM x
            , text " and " <+> prettyTCM y]) mzero
    case p of
      PWild  -> yes
      PVar i -> tellSubst i v
      PDef f ps -> do
        v <- liftRed $ constructorForm v
        case ignoreSharing v of
          Def f' es
            | f == f'   -> matchArgs ps es
            | otherwise -> no f f'
          Con c vs
            | f == conName c -> matchArgs ps (Apply <$> vs)
            | otherwise -> no f c
          MetaV m es -> do
            matchingBlocked $ Blocked m ()
          _ -> no p v
      PTerm u -> tellEq u v
    where
      matchArgs :: [Elim' NLPat] -> Elims -> NLM ()
      matchArgs ps es = ambMatch ps =<< liftRed (etaContract =<< reduce' es)

makeSubstitution :: IntMap Term -> Substitution
makeSubstitution sub
  | IntMap.null sub = idS
  | otherwise       = map val [0 .. highestIndex] ++# raiseS (highestIndex + 1)
  where
    highestIndex = fst $ IntMap.findMax sub  -- find highest key
    val i = fromMaybe (var i) $ IntMap.lookup i sub

disambiguateSubstitution :: AmbSubst -> ReduceM (Maybe Substitution)
disambiguateSubstitution as = do
  mvs <- forM (ambSubst as) $ \vs -> case vs of
    [] -> __IMPOSSIBLE__ -- unbound variable
    (v:vs) -> do
      ok <- andM (equal v <$> vs)
      if ok then return (Just v) else return Nothing
  case sequence mvs of
    Nothing -> return Nothing
    Just vs -> traceSDoc "rewriting" 90 (text $ "vs = " ++ show vs) $ return $ Just $ makeSubstitution vs

checkPostponedEquations :: Substitution -> PostponedEquations -> ReduceM Bool
checkPostponedEquations sub eqs = andM $ for eqs $
  \ (PostponedEquation lhs rhs) -> equal (applySubst sub lhs) rhs

-- main function
nonLinMatch :: (AmbMatch a b) => a -> b -> ReduceM (Either Blocked_ Substitution)
nonLinMatch p v = do
  let no msg b = traceSDoc "rewriting" 100 (sep
                   [ text "matching failed during" <+> text msg
                   , text "blocking: " <+> text (show b) ]) $ return (Left b)
  caseEitherM (runNLM $ ambMatch p v) (no "ambiguous matching") $ \ (asub, eqs) -> do
    sub <- disambiguateSubstitution asub
    traceSDoc "rewriting" 90 (text $ "sub = " ++ show sub) $ case sub of
      Nothing  -> no "disambiguation" $ NotBlocked ReallyNotBlocked ()
                  -- actually we are blocked, but we don't really know what we're blocked on...
      Just sub -> do
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
