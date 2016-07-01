{-# LANGUAGE CPP               #-}

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
recovered from dot patterns.  In the epic backend,
@
  unsing : {A : Set} (x : A) -> Sing x -> A
  unsing .x (sing x) = x
@
becomes
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
unsound for Epic's program extraction, but ok if forcing is only used
to decide which arguments to skip during conversion checking.

From now on, forcing uses equality (I) and does not search for forced
variables under type constructors.  This may lose some savings during
conversion checking.  If this turns out to be a problem, the old
forcing could be brought back, using a new modality @Skip@ to indicate
that this is a relevant argument but still can be skipped during
conversion checking as it is forced by equality (II).

-}

module Agda.TypeChecking.Forcing where

import Prelude hiding (elem, maximum)

import Control.Applicative
import Data.Foldable
import Data.Traversable

import Agda.Interaction.Options

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Irrelevance
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Conversion

import Agda.Utils.Function
import Agda.Utils.Monad
import Agda.Utils.Size

#include "undefined.h"
import Agda.Utils.Impossible

-- | Given the type of a constructor (excluding the parameters),
--   decide which arguments are forced.
--   Update the relevance info in the domains accordingly.
--   Precondition: the type is of the form @Γ → D vs@ and the @vs@
--   are in normal form.
addForcingAnnotations :: Type -> TCM Type
addForcingAnnotations t =
  ifM (not . optForcing <$> commandLineOptions)
      (return t) $ do
  -- Andreas, 2015-03-10  Normalization prevents Issue 1454.
  -- t <- normalise t
  -- Andreas, 2015-03-28  Issue 1469: Normalization too costly.
  -- Instantiation also fixes Issue 1454.
  -- Note that normalization of s0 below does not help.
  t <- instantiateFull t
  let TelV tel (El s a) = telView' t
      vs = case ignoreSharing a of
        Def _ us -> us
        _        -> __IMPOSSIBLE__
      n  = size tel
      indexToLevel x = n - x - 1
  -- Note: data parameters will be negative levels.
  let xs = filter (>=0) $ map indexToLevel $ forcedVariables vs
  let s0 = raise (0 - size tel) s
  t' <- force s0 xs t
  reportSLn "tc.force" 60 $ unlines
    [ "Forcing analysis"
    , "  xs = " ++ show xs
    , "  t  = " ++ show t
    , "  t' = " ++ show t'
    ]
  return t'

-- | Compute the pattern variables of a term or term-like thing.
class ForcedVariables a where
  forcedVariables :: a -> [Nat]

instance (ForcedVariables a, Foldable t) => ForcedVariables (t a) where
  forcedVariables = foldMap forcedVariables

-- | Assumes that the term is in normal form.
instance ForcedVariables Term where
  forcedVariables t = case ignoreSharing t of
    Var i [] -> [i]
    Con _ vs -> forcedVariables vs
    _        -> []

-- | @force s xs t@ marks the domains @xs@ in function type @t@ as forced.
--   Domains bigger than @s@ are marked as @'Forced' 'Big'@, others as
--   @'Forced' 'Small'@.
--   Counting left-to-right, starting with 0.
--   Precondition: function type is exposed.
force :: Sort -> [Nat] -> Type -> TCM Type
force s0 xs t = loop 0 t
  where
    m = maximum (-1:xs)  -- number of domains to look at
    loop i t | i > m = return t
    loop i t = case ignoreSharingType t of
      El s (Pi a b) -> do
        a' <- if not (i `elem` xs) then return a else do
          -- If the sort of the data type is >= the sort of the argument type
          -- then the index is small, else big.
          b <- ifM (tryConversion $ leqSort (getSort a) (raise i s0)) (return Small) (return Big)
          return $ mapRelevance (composeRelevance $ Forced b) a
        El s . Pi a' <$> traverse (loop $ i + 1) b
      _ -> __IMPOSSIBLE__
