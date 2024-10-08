
{-| A constructor argument is forced if it appears as pattern variable
in an index of the target.

For instance @x@ is forced in @sing@ and @n@ is forced in @zero@ and @suc@:

@
  data Sing {a}{A : Set a} : A -> Set where
    sing : (x : A) -> Sing x

  data Fin : Nat -> Set where
    zero : (n : Nat) -> Fin (suc n)
    suc  : (n : Nat) (i : Fin n) -> Fin (suc n)
@

At runtime, forced constructor arguments may be erased as they can be
recovered from dot patterns.  For instance,
@
  unsing : {A : Set} (x : A) -> Sing x -> A
  unsing .x (sing x) = x
@
can become
@
  unsing x sing = x
@
and
@
  proj : (n : Nat) (i : Fin n) -> Nat
  proj .(suc n) (zero n) = n
  proj .(suc n) (suc n i) = n
@
becomes
@
  proj (suc n) zero    = n
  proj (suc n) (suc i) = n
@

This module implements the analysis of which constructor arguments are forced. The process of moving
the binding site of forced arguments is implemented in the unifier (see the Solution step of
Agda.TypeChecking.Rules.LHS.Unify.unifyStep).

Forcing is a concept from pattern matching and thus builds on the
concept of equality (I) used there (closed terms, extensional) which is
different from the equality (II) used in conversion checking and the
constraint solver (open terms, intensional).

Up to issue 1441 (Feb 2015), the forcing analysis here relied on the
wrong equality (II), considering type constructors as injective.  This is
unsound for program extraction, but ok if forcing is only used to decide which
arguments to skip during conversion checking.

From now on, forcing uses equality (I) and does not search for forced
variables under type constructors.  This may lose some savings during
conversion checking.  If this turns out to be a problem, the old
forcing could be brought back, using a new modality @Skip@ to indicate
that this is a relevant argument but still can be skipped during
conversion checking as it is forced by equality (II).

-}

module Agda.TypeChecking.Forcing
  ( computeForcingAnnotations,
    isForced,
    nextIsForced ) where

import Control.Monad.Reader ( MonadReader, ask, local, ReaderT, runReaderT )
import Control.Monad.State  ( MonadState, modify, StateT, execStateT )

import Data.Bifunctor
import Data.Function ((&))
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Monoid -- for (<>) in GHC 8.0.2

import Agda.Interaction.Options

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Datatypes (consOfHIT)
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope

import Agda.Utils.Boolean (implies)
import Agda.Utils.IArray (Array, listArray)
import qualified Agda.Utils.IArray as Array
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Syntax.Common.Pretty (prettyShow)
import Agda.Utils.Size
import Agda.Utils.Singleton

import Agda.Utils.Impossible

-- | Given the type of a constructor (excluding the parameters),
--   decide which arguments are forced.
computeForcingAnnotations :: QName -> Type -> TCM [IsForced]
computeForcingAnnotations c t =
  ifNotM (optForcing <$> pragmaOptions {-then-}) (return []) $ {-else-} do
    -- Andreas, 2015-03-10  Normalization prevents Issue 1454.
    -- t <- normalise t
    -- Andreas, 2015-03-28  Issue 1469: Normalization too costly.
    -- Instantiation also fixes Issue 1454.
    -- Note that normalization of s0 below does not help.
    -- t <- instantiateFull t
    -- Ulf, 2018-01-28 (#2919): We do need to reduce the target type enough to
    -- get to the actual data type.
    -- Also #2947: The type might reduce to a pi type.
    -- Andreas, 2024-07-07, issue #6744, iteratively reduce.
    TelV tel (El _ a) <- telViewPath t
    erasureOn <- optErasure <$> pragmaOptions
    -- Modalities of constructor arguments:
    let n = size tel
        -- Candidates for forced arguments, indexed by their de Bruijn index.
        -- 'Nothing' means cannot possibly be forced.
        forcedArgCands :: ForcedVariableCandidates
        forcedArgCands = listArray (0,n-1)
          [ -- Jesper, 2023-09-20 (#6867): With --erasure, only arguments with @0 can be forced.
            if (erasureOn `implies` hasQuantity0 m)
            -- Also the argument shouldn't be irrelevant, since in that
            -- case it isn't really forced.
            && (not $ isIrrelevant m)
            then Just m else Nothing
          | m <- map getModality $ reverse $ telToList tel
          ]
    -- Computation of forced arguments:
    let vs = case a of
          Def _ us -> us
          _        -> __IMPOSSIBLE__
    forcedVars <-
          -- No candidates, no winners!
      if all isNothing forcedArgCands then pure IntSet.empty
      else runReduceM $ execForcedVariableCollection forcedArgCands $ forcedVariables vs
    let forcedArgs =
          [ if IntSet.member i forcedVars then Forced else NotForced
          | i <- downFrom n
          ]
    reportS "tc.force" 60
      [ "Forcing analysis for " ++ prettyShow c
      , "  forcedVars  = " ++ show (IntSet.toList forcedVars)
      , "  forcedArgs  = " ++ show forcedArgs
      ]
    return forcedArgs

-- | Candidates for forced constructor arguments (@Just m@) with their modality (@m@)
--   in the constructor telescope.
--
type ForcedVariableCandidates = Array Nat (Maybe Modality)

-- | Environment for forced variable collection.
--
data ForcedVariableContext = ForcedVariableContext
  { fvcModality   :: Modality
      -- ^ Modality of current position.  (Accumulated from traversed 'Arg's.)
  , fvcCandidates :: ForcedVariableCandidates
      -- ^ Candidates for forced variables.  (Immutable.)
  }

-- | Which candidates are actually forced?
--
type ForcedVariableState = IntSet

-- | Monad for forced variable analysis.
--
newtype ForcedVariableCollection' a = ForcedVariableCollection
  { runForcedVariableCollection :: ReaderT ForcedVariableContext (StateT ForcedVariableState ReduceM) a }
  deriving
    ( Functor, Applicative, Monad
    , MonadReader ForcedVariableContext, MonadState ForcedVariableState
    -- Needed for HasConstInfo:
    , MonadDebug, MonadTCEnv, HasOptions
    , HasConstInfo
    -- Neded for MonadReduce:
    , ReadTCState
    , MonadReduce
    )

type ForcedVariableCollection = ForcedVariableCollection' ()

instance Semigroup ForcedVariableCollection where
  ForcedVariableCollection m <> ForcedVariableCollection m' = ForcedVariableCollection (m >> m')

instance Monoid ForcedVariableCollection where
  mempty = ForcedVariableCollection $ pure ()

instance Singleton (Nat, Modality) ForcedVariableCollection where
  singleton (i, m) = ForcedVariableCollection do
    ForcedVariableContext mc cands <- ask
    whenJust (join $ cands Array.!? i) \ m0 -> do
      -- #2819: We can only mark an argument as forced if it appears in the
      -- type with a relevance below (i.e. more relevant) than the one of the
      -- constructor argument. Otherwise we can't actually get the value from
      -- the type.
      when (composeModality mc m `moreUsableModality` m0) do
        modify $ IntSet.insert i

-- | Step into an argument labelled with the given modality.
--
underModality :: Modality -> ForcedVariableCollection -> ForcedVariableCollection
underModality m = local \ (ForcedVariableContext mc cands) -> ForcedVariableContext (composeModality mc m) cands

-- | Run the forced variable analysis monad.
execForcedVariableCollection :: ForcedVariableCandidates -> ForcedVariableCollection -> ReduceM ForcedVariableState
execForcedVariableCollection cands (ForcedVariableCollection m) =
  m & (`runReaderT` cxt)
    & (`execStateT` IntSet.empty)
  where cxt = ForcedVariableContext unitModality cands

-- | Compute the pattern variables of a term or term-like thing.
class ForcedVariables a where
  forcedVariables :: a -> ForcedVariableCollection

  default forcedVariables ::
    (ForcedVariables b, Foldable t, a ~ t b) =>
    a -> ForcedVariableCollection
  forcedVariables = foldMap forcedVariables

instance ForcedVariables a => ForcedVariables [a] where

-- Note that the 'a' does not include the 'Arg' in 'Apply'.
instance ForcedVariables a => ForcedVariables (Elim' a) where
  forcedVariables (Apply x) = forcedVariables x
  forcedVariables IApply{}  = mempty  -- No forced variables in path applications
  forcedVariables Proj{}    = mempty

instance ForcedVariables a => ForcedVariables (Arg a) where
  forcedVariables x =
    underModality m $ forcedVariables $ unArg x
    where m = getModality x

-- | Assumes that the term is in normal form.
instance ForcedVariables Term where
  -- Andreas, 2024-07-07, issue #6744, add reduction.
  forcedVariables v = reduce v >>= \case
    Var i []   -> singleton (i, unitModality)
    Con c _ vs -> ifM (consOfHIT $ conName c) mempty $ {-else-} forcedVariables vs
    _          -> mempty

isForced :: IsForced -> Bool
isForced Forced    = True
isForced NotForced = False

nextIsForced :: [IsForced] -> (IsForced, [IsForced])
nextIsForced []     = (NotForced, [])
nextIsForced (f:fs) = (f, fs)
