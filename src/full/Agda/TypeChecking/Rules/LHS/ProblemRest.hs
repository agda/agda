{-# LANGUAGE CPP           #-}

module Agda.TypeChecking.Rules.LHS.ProblemRest where

import Control.Arrow (first, second)

import Data.Functor ((<$))

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Abstract.Pattern
import qualified Agda.Syntax.Abstract as A

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Substitute

import Agda.TypeChecking.Rules.LHS.Problem
import Agda.TypeChecking.Rules.LHS.Implicit

import Agda.Utils.Functor (($>))
import Agda.Utils.List
import Agda.Utils.Size
import Agda.Utils.Permutation

#include "undefined.h"
import Agda.Utils.Impossible

-- | Rename the variables in a telescope using the names from a given pattern.
--
--   Precondition: we have at least as many patterns as entries in the telescope.
--
useNamesFromPattern :: [NamedArg A.Pattern] -> Telescope -> Telescope
useNamesFromPattern ps tel
  | size tel > length ps = __IMPOSSIBLE__
  | otherwise            = telFromList $ zipWith ren ps $ telToList tel
  where
    ren (Arg ai (Named nm p)) dom@(Dom info (y, a)) =
      case p of
        -- Andreas, 2017-10-12, issue #2803, also preserve user-written hidden names.
        -- However, not if the argument is named, because then the name in the telescope
        -- is significant for implicit insertion.
        A.VarP x | not (isNoName x)
                 , visible info || (getOrigin ai == UserWritten && nm == Nothing) ->
          Dom info (nameToArgName x, a)
        A.PatternSynP{} -> __IMPOSSIBLE__  -- ensure there are no syns left
        -- Andreas, 2016-05-10, issue 1848: if context variable has no name, call it "x"
        _ | visible info && isNoName y -> Dom info (stringToArgName "x", a)
          | otherwise                  -> dom

useOriginFrom :: (LensOrigin a, LensOrigin b) => [a] -> [b] -> [a]
useOriginFrom = zipWith $ \x y -> setOrigin (getOrigin y) x

-- | Are there any untyped user patterns left?
noProblemRest :: Problem a -> Bool
noProblemRest (Problem _ rp _ _ _) = null rp

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
  :: [NamedArg A.Pattern] -- ^ The user patterns.
  -> Type                 -- ^ The type the user patterns eliminate.
  -> (LHSState a -> TCM a) -- ^ Continuation for when checking the patterns is complete.
  -> TCM (LHSState a)     -- ^ The initial LHS state constructed from the user patterns.
initLHSState ps0 a ret = do
  -- Andreas, 2017-01-18, issue #819: We set all A.WildP origins to Inserted
  -- in order to guide the pattern printer to discard variable names it made up.
  let ps = (`mapNamedArgPattern` ps0) $ \case
        p | A.WildP{} <- namedArg p -> setOrigin Inserted p
        p -> p
      problem = Problem [] ps [] [] ret

  updateProblemRest $ LHSState EmptyTel [] problem (defaultArg a)

-- | Try to move patterns from the problem rest into the problem.
--   Possible if type of problem rest has been updated to a function type.
updateProblemRest :: LHSState a -> TCM (LHSState a)
updateProblemRest st@(LHSState tel0 qs0 p@(Problem ps0 ps dpi sbe ret) a) = do
      ps <- insertImplicitPatternsT ExpandLast ps $ unArg a
      reportSDoc "tc.lhs.imp" 20 $
        text "insertImplicitPatternsT returned" <+> fsep (map prettyA ps)
      -- (Issue 734: Do only the necessary telView to preserve clause types as much as possible.)
      TelV tel b   <- telViewUpTo (length ps) $ unArg a
      let gamma     = useNamesFromPattern ps tel
          n         = size gamma
          (ps1,ps2) = splitAt n ps
          tel1      = telFromList $ telToList tel0 ++ telToList gamma
          qs1       = teleNamedArgs gamma `useOriginFrom` ps
          tau       = raiseS n
      reportSDoc "tc.lhs.problem" 10 $ addContext tel0 $ vcat
        [ text "checking lhs -- updated split problem:"
        , nest 2 $ vcat
          [ text "ps    =" <+> fsep (map prettyA ps)
          , text "a     =" <+> prettyTCM a
          , text "tel   =" <+> prettyTCM tel
          , text "gamma =" <+> prettyTCM gamma
          , text "ps1   =" <+> fsep (map prettyA ps1)
          , text "ps2   =" <+> fsep (map prettyA ps2)
          , text "b     =" <+> addContext gamma (prettyTCM b)
          ]
        ]
      return $ LHSState
        { lhsTel     = tel1
        , lhsOutPat  = applySubst (raiseS n) qs0 ++ qs1
        , lhsProblem = Problem
                       { problemInPat    = ps0 ++ ps1
                       , problemRestPats = ps2
                       , problemDPI      = applyPatSubst tau dpi
                       , problemShouldBeEmptyTypes = applyPatSubst tau sbe
                       , problemCont     = ret
                       }
        , lhsTarget  = a $> b
        }
