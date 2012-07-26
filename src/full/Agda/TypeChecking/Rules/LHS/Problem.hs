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

import Agda.TypeChecking.Substitute

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

{- TRASH
  | NoProblemRest                     -- ^ no outstanding user patterns

-- | Smart constructor.  Creates a 'NoProblemRest' when list of patterns is empty.
mkProblemRest :: [NamedArg A.Pattern] -> Type -> ProblemRest
mkProblemRest [] a = NoProblemRest
mkProblemRest ps a = ProblemRest ps a
-}

data Focus	    = Focus   { focusCon      :: QName
			      , focusConArgs  :: [NamedArg A.Pattern]
			      , focusRange    :: Range
			      , focusOutPat   :: OneHolePatterns
			      , focusHoleIx   :: Int  -- ^ index of focused variable in the out patterns
			      , focusDatatype :: QName
			      , focusParams   :: [Arg Term]
			      , focusIndices  :: [Arg Term]
                              , focusType     :: Type -- type of variable we are splitting, kept for record patterns (Andreas, 2010-09-09)
			      }
		    | LitFocus Literal OneHolePatterns Int Type
data SplitProblem   = Split ProblemPart [Name] (Arg Focus) (Abs ProblemPart)
                      -- ^ the [Name]s give the as-bindings for the focus

data SplitError	    = NothingToSplit
		    | SplitPanic String

type ProblemPart = Problem' ()

instance Raise ProblemRest where
  raiseFrom  m k p = p { restType = raiseFrom  m k $ restType p }
  renameFrom m k p = p { restType = renameFrom m k $ restType p }

instance Raise (Problem' p) where
  raiseFrom  m k p = p { problemTel  = raiseFrom  m k $ problemTel p
                       , problemRest = raiseFrom  m k $ problemRest p }
  renameFrom m k p = p { problemTel  = renameFrom m k $ problemTel p
                       , problemRest = renameFrom m k $ problemRest p }

-- | The permutation should permute @allHoles@ of the patterns to correspond to
--   the abstract patterns in the problem.
type Problem	 = Problem' (Permutation, [Arg Pattern])

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

{- TRASH
instance Monoid ProblemRest where
  mempty = NoProblemRest
  mappend pr NoProblemRest = pr

-- | 'ProblemRest' is not really a monoid.
--   We can only compose the empty 'ProblemRest' with some other 'ProblemRest'
--   (left unit law).
instance Monoid ProblemRest where
  mempty = ProblemRest [] typeDontCare
  mappend (ProblemRest [] _) pr = pr
  mappend (ProblemRest (_ : _) _) pr = __IMPOSSIBLE__
-}

instance Monoid p => Monoid (Problem' p) where
  mempty = Problem [] mempty EmptyTel mempty
  Problem ps1 qs1 tel1 pr1 `mappend` Problem ps2 qs2 tel2 pr2 =
    Problem (ps1 ++ ps2) (mappend qs1 qs2) (abstract tel1 tel2) (mappend pr1 pr2)
