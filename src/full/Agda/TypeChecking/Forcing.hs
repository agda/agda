{-# LANGUAGE CPP               #-}
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

module Agda.TypeChecking.Forcing where

import Prelude hiding (elem, maximum)

import Data.Foldable hiding (any)
import Data.Traversable
import Data.Semigroup hiding (Arg)

import Agda.Interaction.Options

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Irrelevance
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute

import Agda.Utils.Function
import Agda.Utils.PartialOrd
import Agda.Utils.Pretty (prettyShow)
import Agda.Utils.List
import Agda.Utils.Monad
import Agda.Utils.Size

#include "undefined.h"
import Agda.Utils.Impossible

-- | Given the type of a constructor (excluding the parameters),
--   decide which arguments are forced.
--   Precondition: the type is of the form @Γ → D vs@ and the @vs@
--   are in normal form.
computeForcingAnnotations :: Type -> TCM [IsForced]
computeForcingAnnotations t =
  ifM (not . optForcing <$> commandLineOptions)
      (return []) $ do
  -- Andreas, 2015-03-10  Normalization prevents Issue 1454.
  -- t <- normalise t
  -- Andreas, 2015-03-28  Issue 1469: Normalization too costly.
  -- Instantiation also fixes Issue 1454.
  -- Note that normalization of s0 below does not help.
  t <- instantiateFull t
  let TelV tel (El _ a) = telView' t
      vs = case ignoreSharing a of
        Def _ us -> us
        _        -> __IMPOSSIBLE__
      n  = size tel
      xs = forcedVariables vs
      -- #2819: We can only mark an argument as forced if it appears in the
      -- type with a relevance below (i.e. more relevant) than the one of the
      -- constructor argument. Otherwise we can't actually get the value from
      -- the type.
      isForced m i = any (\ (m', j) -> i == j && related m' POLE m) xs
      forcedArgs =
        [ if isForced m i then Forced else NotForced
        | (i, m) <- zip (downFrom n) $ map getModality (telToList tel)
        ]
  reportSLn "tc.force" 60 $ unlines
    [ "Forcing analysis"
    , "  xs          = " ++ show xs
    , "  forcedArgs  = " ++ show forcedArgs
    ]
  return forcedArgs

-- | Compute the pattern variables of a term or term-like thing.
class ForcedVariables a where
  forcedVariables :: a -> [(Modality, Nat)]

  default forcedVariables :: (ForcedVariables b, Foldable t, a ~ t b) => a -> [(Modality, Nat)]
  forcedVariables = foldMap forcedVariables

instance ForcedVariables a => ForcedVariables [a] where

-- Note the 'a' does not include the 'Arg' in 'Apply'.
instance ForcedVariables a => ForcedVariables (Elim' a) where
  forcedVariables (Apply x) = forcedVariables x
  forcedVariables Proj{} = []

instance ForcedVariables a => ForcedVariables (Arg a) where
  forcedVariables x = [ (m <> m', i) | (m', i) <- forcedVariables (unArg x) ]
    where m = getModality x

-- | Assumes that the term is in normal form.
instance ForcedVariables Term where
  forcedVariables t = case ignoreSharing t of
    Var i [] -> [(mempty, i)]
    Con _ _ vs -> forcedVariables vs
    _ -> []

isForced :: IsForced -> Bool
isForced Forced    = True
isForced NotForced = False

nextIsForced :: [IsForced] -> (IsForced, [IsForced])
nextIsForced []     = (NotForced, [])
nextIsForced (f:fs) = (f, fs)
