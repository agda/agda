
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

type Substitution   = [Maybe Term]
type FlexibleVars   = [Nat]

data Problem' p	    = Problem { problemInPat  :: [NamedArg A.Pattern]
			      , problemOutPat :: p
			      , problemTel    :: Telescope
			      }
data Focus	    = Focus   { focusCon      :: QName
			      , focusConArgs  :: [NamedArg A.Pattern]
			      , focusRange    :: Range
			      , focusOutPat   :: OneHolePatterns
			      , focusHoleIx   :: Int  -- ^ index of focused variable in the out patterns
			      , focusDatatype :: QName
			      , focusParams   :: [Arg Term]
			      , focusIndices  :: [Arg Term]
			      }
		    | LitFocus Literal OneHolePatterns Int Type
data SplitProblem   = Split ProblemPart [Name] (Arg Focus) (Abs ProblemPart)
                      -- ^ the [Name]s give the as-bindings for the focus

data SplitError	    = NothingToSplit
		    | SplitPanic String

type ProblemPart = Problem' ()

-- | The permutation should permute @allHoles@ of the patterns to correspond to
--   the abstract patterns in the problem.
type Problem	 = Problem' (Permutation, [Arg Pattern])

instance Error SplitError where
  noMsg  = NothingToSplit
  strMsg = SplitPanic

instance Monoid p => Monoid (Problem' p) where
  mempty = Problem [] mempty EmptyTel
  Problem ps1 qs1 tel1 `mappend` Problem ps2 qs2 tel2 =
    Problem (ps1 ++ ps2) (mappend qs1 qs2) (abstract tel1 tel2)

