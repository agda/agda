{-# LANGUAGE CPP, TupleSections #-}

module Agda.TypeChecking.Rules.LHS.ProblemRest where

import Control.Applicative

import Data.Monoid

import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Info
import Agda.Syntax.Internal
import qualified Agda.Syntax.Abstract as A

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Implicit
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Pretty

import Agda.TypeChecking.Rules.LHS.Problem
import Agda.TypeChecking.Rules.LHS.Implicit

import Agda.Utils.Size
import Agda.Utils.Permutation

#include "../../../undefined.h"
import Agda.Utils.Impossible


-- MOVED from LHS:
-- | Rename the variables in a telescope using the names from a given pattern
useNamesFromPattern :: [NamedArg A.Pattern] -> Telescope -> Telescope
useNamesFromPattern ps = telFromList . zipWith ren (toPats ps ++ repeat dummy) . telToList
  where
    dummy = A.WildP __IMPOSSIBLE__
    ren (A.VarP x) (Dom NotHidden r (_, a)) = Dom NotHidden r (show x, a)
    ren A.PatternSynP{} _ = __IMPOSSIBLE__  -- ensure there are no syns left
    ren _ a = a
    toPats = map namedArg

-- | Are there any untyped user patterns left?
noProblemRest :: Problem -> Bool
noProblemRest (Problem _ _ _ (ProblemRest ps _)) = null ps

-- | Get the type of clause.  Only valid if 'noProblemRest'.
typeFromProblem :: Problem -> Type
typeFromProblem (Problem _ _ _ (ProblemRest _ a)) = a

-- | Construct an initial 'split' 'Problem' from user patterns.
problemFromPats :: [NamedArg A.Pattern] -- ^ The user patterns.
  -> Type            -- ^ The type the user patterns eliminate.
  -> TCM Problem     -- ^ The initial problem constructed from the user patterns.
problemFromPats ps a = do
  TelV tel0' b0 <- telView a
  -- For the initial problem, do not insert trailing implicits.
  -- This has the effect of not including trailing hidden domains in the problem telescope.
  -- In all later call to insertImplicitPatterns, we can then use ExpandLast.
  ps <- insertImplicitPatterns DontExpandLast ps tel0'
  -- unless (size tel0' >= size ps) $ typeError $ TooManyArgumentsInLHS a
  let tel0      = useNamesFromPattern ps tel0'
      (as, bs)  = splitAt (size ps) $ telToList tel0
      (ps1,ps2) = splitAt (size as) ps
      gamma     = telFromList as
      b         = telePi (telFromList bs) b0
      -- now (gamma -> b) = a and |gamma| = |ps1|
      pr        = ProblemRest ps2 b
      -- patterns ps2 eliminate type b

      -- internal patterns start as all variables
      ips      = map (argFromDom . fmap (VarP . fst)) as

      -- the initial problem for starting the splitting
      problem  = Problem ps1 (idP $ size ps1, ips) gamma pr
  reportSDoc "tc.lhs.problem" 10 $
    vcat [ text "checking lhs -- generated an initial split problem:"
	 , nest 2 $ vcat
	   [ text "ps    =" <+> fsep (map prettyA ps)
	   , text "a     =" <+> prettyTCM a
	   , text "a'    =" <+> prettyTCM (telePi tel0  b0)
	   , text "a''   =" <+> prettyTCM (telePi tel0' b0)
           , text "xs    =" <+> text (show $ map (fst . unDom) as)
	   , text "tel0  =" <+> prettyTCM tel0
	   , text "b0    =" <+> prettyTCM b0
	   , text "gamma =" <+> prettyTCM gamma
	   , text "b     =" <+> addCtxTel gamma (prettyTCM b)
	   ]
	 ]
  return problem

{-
todoProblemRest :: ProblemRest
todoProblemRest = mempty
-}

-- | Try to move patterns from the problem rest into the problem.
--   Possible if type of problem rest has been updated to a function type.
updateProblemRest_ :: Problem -> TCM (Nat, Problem)
updateProblemRest_ p@(Problem _ _ _ (ProblemRest [] _)) = return (0, p)
updateProblemRest_ p@(Problem ps0 (perm0@(Perm n0 is0), qs0) tel0 (ProblemRest ps a)) = do
  TelV tel' b0 <- telView a
  case tel' of
    EmptyTel -> return (0, p)  -- no progress
    ExtendTel{} -> do     -- a did reduce to a pi-type
      ps <- insertImplicitPatterns DontExpandLast ps tel'
      let tel       = useNamesFromPattern ps tel'
          (as, bs)  = splitAt (size ps) $ telToList tel
          (ps1,ps2) = splitAt (size as) ps
          tel1      = telFromList $ telToList tel0 ++ as
          b         = telePi (telFromList bs) b0
          pr        = ProblemRest ps2 b
          qs1       = map (argFromDom . fmap (VarP . fst)) as
          n         = size as
          perm1     = liftP n perm0 -- IS: Perm (n0 + n) $ is0 ++ [n0..n0+n-1]
      return $ (n,) $ Problem (ps0 ++ ps1) (perm1, raise n qs0 ++ qs1) tel1 pr

updateProblemRest :: LHSState -> TCM LHSState
updateProblemRest st@LHSState { lhsProblem = p } = do
  (n, p') <- updateProblemRest_ p
  if (n == 0) then return st else do
    let tau = raiseS n
    return $ LHSState
      { lhsProblem = p'
      , lhsSubst   = applySubst tau (lhsSubst st)
      , lhsDPI     = applySubst tau (lhsDPI st)
      , lhsAsB     = applySubst tau (lhsAsB st)
      }
