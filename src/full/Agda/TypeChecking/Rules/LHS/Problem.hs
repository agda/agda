{-# LANGUAGE CPP #-}
module Agda.TypeChecking.Rules.LHS.Problem where

import Control.Monad.Error
import Data.Monoid

import Agda.Syntax.Common
import Agda.Syntax.Literal
import Agda.Syntax.Position
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern
import qualified Agda.Syntax.Abstract as A

import Agda.TypeChecking.Substitute as S
import Agda.TypeChecking.Pretty

import Agda.Utils.Permutation

{- UNUSED
#include "../../../undefined.h"
import Agda.Utils.Impossible
-}

type Substitution   = [Maybe Term]
type FlexibleVars   = [Nat]

-- | State of typechecking a LHS; input to 'split'.
--   [Ulf Norell's PhD, page. 35]
--
--   In @Problem ps p delta@,
--   @ps@ are the user patterns of supposed type @delta@.
--   @p@ is the pattern resulting from the splitting.
data Problem' p	    = Problem { problemInPat  :: [NamedArg A.Pattern]
			      , problemOutPat :: p
			      , problemTel    :: Telescope
                              , problemRest   :: ProblemRest
			      }

-- | User patterns that could not be given a type yet.
--
--   Example:
--   @
--      f : (b : Bool) -> if b then Nat else Nat -> Nat
--      f true          = zero
--      f false zero    = zero
--      f false (suc n) = n
--   @
--   In this sitation, for clause 2, we construct an initial problem
--   @
--      problemInPat = [false]
--      problemTel   = (b : Bool)
--      problemRest.restPats = [zero]
--      problemRest.restType = if b then Nat else Nat -> Nat
--   @
--   As we instantiate @b@ to @false@, the 'restType' reduces to
--   @Nat -> Nat@ and we can move pattern @zero@ over to @problemInPat@.
data ProblemRest    = ProblemRest
  { restPats :: [NamedArg A.Pattern]  -- ^ non-empty list of user patterns which could not yet be typed
  , restType :: Type                  -- ^ type eliminated by 'restPats'
  }

data Focus	    = Focus   { focusCon      :: QName
			      , focusConArgs  :: [NamedArg A.Pattern]
			      , focusRange    :: Range
			      , focusOutPat   :: OneHolePatterns
			      , focusHoleIx   :: Int  -- ^ Index of focused variable in the out patterns.
			      , focusDatatype :: QName
			      , focusParams   :: [Arg Term]
			      , focusIndices  :: [Arg Term]
                              , focusType     :: Type -- ^ Type of variable we are splitting, kept for record patterns.
			      }
		    | LitFocus Literal OneHolePatterns Int Type

data SplitProblem   = Split ProblemPart [Name] (Arg Focus) (Abs ProblemPart)
                      -- ^ the [Name]s give the as-bindings for the focus

data SplitError	    = NothingToSplit
		    | SplitPanic String

-- | The permutation should permute @allHoles@ of the patterns to correspond to
--   the abstract patterns in the problem.
type Problem	 = Problem' (Permutation, [Arg Pattern])
type ProblemPart = Problem' ()

data DotPatternInst = DPI A.Expr Term (Dom Type)
data AsBinding      = AsB Name Term Type

-- | State worked on during the main loop of checking a lhs.
data LHSState = LHSState
  { lhsProblem :: Problem
  , lhsSubst   :: S.Substitution
  , lhsDPI     :: [DotPatternInst]
  , lhsAsB     :: [AsBinding]
  }

instance Subst ProblemRest where
  applySubst rho p = p { restType = applySubst rho $ restType p }

instance Subst (Problem' p) where
  applySubst rho p = p { problemTel  = applySubst rho $ problemTel p
                       , problemRest = applySubst rho $ problemRest p }

instance Subst DotPatternInst where
  applySubst rho (DPI e v a) = uncurry (DPI e) $ applySubst rho (v,a)

instance Subst AsBinding where
  applySubst rho (AsB x v a) = uncurry (AsB x) $ applySubst rho (v, a)

instance PrettyTCM DotPatternInst where
  prettyTCM (DPI e v a) = sep
    [ prettyA e <+> text "="
    , nest 2 $ prettyTCM v <+> text ":"
    , nest 2 $ prettyTCM a
    ]

instance PrettyTCM AsBinding where
  prettyTCM (AsB x v a) =
    sep [ prettyTCM x <> text "@" <> parens (prettyTCM v)
        , nest 2 $ text ":" <+> prettyTCM a
        ]

instance Error SplitError where
  noMsg  = NothingToSplit
  strMsg = SplitPanic

-- | 'ProblemRest' is a right dominant monoid.
--   @pr1 \`mappend\` pr2 = pr2@ unless @pr2 = mempty@, then it is @pr1@.
--   Basically, this means that the left 'ProblemRest' is discarded, so
--   use it wisely!
instance Monoid ProblemRest where
  mempty = ProblemRest [] typeDontCare
  mappend pr (ProblemRest [] _) = pr
  mappend _  pr                 = pr

instance Monoid p => Monoid (Problem' p) where
  mempty = Problem [] mempty EmptyTel mempty
  Problem ps1 qs1 tel1 pr1 `mappend` Problem ps2 qs2 tel2 pr2 =
    Problem (ps1 ++ ps2) (mappend qs1 qs2) (abstract tel1 tel2) (mappend pr1 pr2)
