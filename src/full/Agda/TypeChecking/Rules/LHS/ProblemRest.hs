
module Agda.TypeChecking.Rules.LHS.ProblemRest where

import Control.Monad

import Data.Maybe

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern
import qualified Agda.Syntax.Abstract as A

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Substitute

import Agda.TypeChecking.Rules.LHS.Problem
import Agda.TypeChecking.Rules.LHS.Implicit

import Agda.Utils.Functor
import Agda.Utils.Size

import Agda.Utils.Impossible

-- | Rename the variables in a telescope using the names from a given pattern.
--
--   If there are not at least as many patterns as entries as in the telescope,
--   the names of the remaining entries in the telescope are unchanged.
--   If there are too many patterns, there should be a type error later.
--
useNamesFromPattern :: [NamedArg A.Pattern] -> Telescope -> Telescope
useNamesFromPattern ps tel = telFromList (zipWith ren ps telList ++ telRemaining)
  where
    telList = telToList tel
    telRemaining = drop (length ps) telList -- telescope entries beyond patterns
    ren (Arg ai (Named nm p)) dom@Dom{ unDom = (y, a) } =
      case p of
        -- Andreas, 2017-10-12, issue #2803, also preserve user-written hidden names.
        -- However, not if the argument is named, because then the name in the telescope
        -- is significant for implicit insertion.
        A.VarP A.BindName{unBind = x}
          | not (isNoName x)
          , visible dom || (getOrigin ai == UserWritten && nm == Nothing) ->
          dom{ unDom = (nameToArgName x, a) }
        A.AbsurdP{} | visible dom -> dom{ unDom = (stringToArgName "()", a) }
        A.PatternSynP{} -> __IMPOSSIBLE__  -- ensure there are no syns left
        -- Andreas, 2016-05-10, issue 1848: if context variable has no name, call it "x"
        _ | visible dom && isNoName y -> dom{ unDom = (stringToArgName "x", a) }
          | otherwise                  -> dom

useNamesFromProblemEqs :: [ProblemEq] -> Telescope -> TCM Telescope
useNamesFromProblemEqs eqs tel = addContext tel $ do
  names <- fst . getUserVariableNames tel . patternVariables <$> getLeftoverPatterns eqs
  let argNames = map (fmap nameToArgName) names
  return $ renameTel argNames tel

useOriginFrom :: (LensOrigin a, LensOrigin b) => [a] -> [b] -> [a]
useOriginFrom = zipWith $ \x y -> setOrigin (getOrigin y) x

-- | Are there any untyped user patterns left?
noProblemRest :: Problem a -> Bool
noProblemRest (Problem _ rp _) = null rp

-- | Construct an initial 'LHSState' from user patterns.
--   Example:
--   @
--
--      Case : {A : Set} → Maybe A → Set → Set → Set
--      Case nothing  B C = B
--      Case (just _) B C = C
--
--      sample : {A : Set} (m : Maybe A) → Case m Bool (Maybe A → Bool)
--      sample (just a) (just b) = true
--      sample (just a) nothing  = false
--      sample nothing           = true
--   @
--   The problem generated for the first clause of @sample@
--   with patterns @just a, just b@ would be:
--   @
--      lhsTel        = [A : Set, m : Maybe A]
--      lhsOutPat     = ["A", "m"]
--      lhsProblem    = Problem ["_", "just a"] [] [] []
--      lhsTarget     = "Case m Bool (Maybe A -> Bool)"
--   @
initLHSState
  :: Telescope             -- ^ The initial telescope @delta@ of parameters.
  -> [ProblemEq]           -- ^ The problem equations inherited from the parent clause (living in @delta@).
  -> [NamedArg A.Pattern]  -- ^ The user patterns.
  -> Type                  -- ^ The type the user patterns eliminate (living in @delta@).
  -> (LHSState a -> TCM a) -- ^ Continuation for when checking the patterns is complete.
  -> TCM (LHSState a)      -- ^ The initial LHS state constructed from the user patterns.
initLHSState delta eqs ps a ret = do
  let problem = Problem eqs ps ret
      qs0     = teleNamedArgs delta

  updateProblemRest $ LHSState delta qs0 problem (defaultArg a) []

-- | Try to move patterns from the problem rest into the problem.
--   Possible if type of problem rest has been updated to a function type.
updateProblemRest :: LHSState a -> TCM (LHSState a)
updateProblemRest st@(LHSState tel0 qs0 p@(Problem oldEqs ps ret) a psplit) = do
  ps <- addContext tel0 $ insertImplicitPatternsT ExpandLast ps $ unArg a
  reportSDoc "tc.lhs.imp" 20 $
    "insertImplicitPatternsT returned" <+> fsep (map prettyA ps)
  -- (Issue 734: Do only the necessary telView to preserve clause types as much as possible.)
  let m = length $ takeWhile (isNothing . A.isProjP) ps
  (TelV gamma b, boundary) <- telViewUpToPathBoundaryP m $ unArg a
  forM_ (zip ps (telToList gamma)) $ \(p, a) ->
    unless (sameHiding p a) $ typeError WrongHidingInLHS
  let tel1      = useNamesFromPattern ps gamma
      n         = size tel1
      (ps1,ps2) = splitAt n ps
      tel       = telFromList $ telToList tel0 ++ telToList tel1
      qs1       = telePatterns tel1 boundary
      newEqs    = zipWith3 ProblemEq
                    (map namedArg ps1)
                    (map (patternToTerm . namedArg) qs1)
                    (flattenTel tel1 `useOriginFrom` ps1)
      tau       = raiseS n
  reportSDoc "tc.lhs.problem" 10 $ addContext tel0 $ vcat
    [ "checking lhs -- updated split problem:"
    , nest 2 $ vcat
      [ "ps    =" <+> fsep (map prettyA ps)
      , "a     =" <+> prettyTCM a
      , "tel1  =" <+> prettyTCM tel1
      , "ps1   =" <+> fsep (map prettyA ps1)
      , "ps2   =" <+> fsep (map prettyA ps2)
      , "b     =" <+> addContext tel1 (prettyTCM b)
      ]
    ]
  reportSDoc "tc.lhs.problem" 60 $ addContext tel0 $ vcat
    [ nest 2 $ vcat
      [ "ps    =" <+> (text . show) ps
      , "a     =" <+> (text . show) a
      , "tel1  =" <+> (text . show) tel1
      , "ps1   =" <+> (text . show) ps1
      , "ps2   =" <+> (text . show) ps2
      , "b     =" <+> (text . show) b
      , "qs1   =" <+> fsep (map pretty qs1)
      ]
    ]
  return $ LHSState
    { _lhsTel     = tel
    , _lhsOutPat  = applySubst tau qs0 ++ qs1
    , _lhsProblem = Problem
                   { _problemEqs      = applyPatSubst tau oldEqs ++ newEqs
                   , _problemRestPats = ps2
                   , _problemCont     = ret
                   }
    , _lhsTarget  = a $> b
    , _lhsPartialSplit = psplit
    }
