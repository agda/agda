{-# LANGUAGE TypeFamilies #-}

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

import Control.Arrow (first)
import Control.Monad
import Control.Monad.Trans.Maybe
import Control.Monad.Writer (WriterT(..), tell, lift)
import Data.Foldable as Fold hiding (any)
import Data.Maybe
import Data.List ((\\))
import Data.Function (on)
import Data.Monoid

import Agda.Interaction.Options

import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Records
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Pretty hiding ((<>))

import Agda.Utils.Functor
import Agda.Utils.List
import Agda.Utils.Monad
import Agda.Utils.Size

import Agda.Utils.Impossible

-- | Given the type of a constructor (excluding the parameters),
--   decide which arguments are forced.
--   Precondition: the type is of the form @Γ → D vs@ and the @vs@
--   are in normal form.
computeForcingAnnotations :: QName -> Type -> TCM [IsForced]
computeForcingAnnotations c t =
  ifNotM (optForcing <$> pragmaOptions) {-then-} (return []) $ {-else-} do
  -- Andreas, 2015-03-10  Normalization prevents Issue 1454.
  -- t <- normalise t
  -- Andreas, 2015-03-28  Issue 1469: Normalization too costly.
  -- Instantiation also fixes Issue 1454.
  -- Note that normalization of s0 below does not help.
  t <- instantiateFull t
  -- Ulf, 2018-01-28 (#2919): We do need to reduce the target type enough to
  -- get to the actual data type.
  -- Also #2947: The type might reduce to a pi type.
  TelV tel (El _ a) <- telViewPath t
  let vs = case a of
        Def _ us -> us
        _        -> __IMPOSSIBLE__
      n  = size tel
      xs :: [(Modality, Nat)]
      xs = forcedVariables vs
      -- #2819: We can only mark an argument as forced if it appears in the
      -- type with a relevance below (i.e. more relevant) than the one of the
      -- constructor argument. Otherwise we can't actually get the value from
      -- the type. Also the argument shouldn't be irrelevant, since in that
      -- case it isn't really forced.
      isForced :: Modality -> Nat -> Bool
      isForced m i = and
        [ hasQuantity0 m || noUserQuantity m   -- User can disable forcing by giving quantity explicitly.
        , getRelevance m /= Irrelevant
        , any (\ (m', j) -> i == j && m' `moreUsableModality` m) xs
        ]
      forcedArgs =
        [ if isForced m i then Forced else NotForced
        | (i, m) <- zip (downFrom n) $ map getModality (telToList tel)
        ]
  reportS "tc.force" 60
    [ "Forcing analysis for " ++ show c
    , "  xs          = " ++ show (map snd xs)
    , "  forcedArgs  = " ++ show forcedArgs
    ]
  return forcedArgs

-- | Compute the pattern variables of a term or term-like thing.
class ForcedVariables a where
  forcedVariables :: a -> [(Modality, Nat)]

  default forcedVariables :: (ForcedVariables b, Foldable t, a ~ t b) => a -> [(Modality, Nat)]
  forcedVariables = foldMap forcedVariables

instance ForcedVariables a => ForcedVariables [a] where

-- Note that the 'a' does not include the 'Arg' in 'Apply'.
instance ForcedVariables a => ForcedVariables (Elim' a) where
  forcedVariables (Apply x) = forcedVariables x
  forcedVariables IApply{}  = []  -- No forced variables in path applications
  forcedVariables Proj{}    = []

instance ForcedVariables a => ForcedVariables (Arg a) where
  forcedVariables x = [ (m <> m', i) | (m', i) <- forcedVariables (unArg x) ]
    where m = getModality x

-- | Assumes that the term is in normal form.
instance ForcedVariables Term where
  forcedVariables t = case t of
    Var i [] -> [(mempty, i)]
    Con _ _ vs -> forcedVariables vs
    _ -> []

isForced :: IsForced -> Bool
isForced Forced    = True
isForced NotForced = False

nextIsForced :: [IsForced] -> (IsForced, [IsForced])
nextIsForced []     = (NotForced, [])
nextIsForced (f:fs) = (f, fs)

