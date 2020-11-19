{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE CPP                        #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE TypeFamilies               #-}

module Agda.TypeChecking.Heterogeneous where

import Prelude hiding (drop, length)

import Data.Coerce
import Data.Data (Data, Typeable)
import Data.Foldable (toList)
import Data.Sequence (Seq)
import qualified Data.Sequence as S

import Agda.Syntax.Abstract.Name
import Agda.Syntax.Concrete.Name (NameInScope(..), LensInScope(..), nameRoot, nameToRawName)
import Agda.Syntax.Internal as I
import Agda.Syntax.Internal.Generic (TermLike(..))
import Agda.Syntax.Position

import Agda.TypeChecking.Monad.Base
import {-# SOURCE #-} Agda.TypeChecking.Monad.Context

import Agda.Utils.Dependent
import Agda.Utils.Monad
import Agda.Utils.Pretty
import qualified Agda.Utils.List

import Agda.Utils.Impossible

----------------------------------------------------------------------
-- * Data structure for a twin type
----------------------------------------------------------------------

--data WithHet' c a = WithHet c a
--type WithHet a = WithHet' ContextHet a

instance Pretty a => Pretty (TwinT' a) where
  pretty (SingleT a) = pretty a
  pretty (TwinT{twinPid,necessary,twinLHS=a,twinRHS=b}) =
    pretty a <> "‡"
             <> (if necessary then "" else "*")
             <> pretty twinPid
             <> pretty b

-- instance (Sing het, Pretty a, Pretty b) => Pretty (If_ het a b) where
--  pretty (If a) = case sing :: SingT het of
--    STrue  -> pretty a
--    SFalse -> pretty a

-- instance AddContextHet (Name, Dom TwinT) where
--   {-# INLINABLE addContextHet #-}
--   addContextHet ctx p κ = κ$ ctx :|> p
--
--instance TwinAt s a => TwinAt s (CompareAs' a) where
--  type TwinAt_ s (CompareAs' a) = CompareAs' (TwinAt_ s a)
--  twinAt = fmap (twinAt @s)

instance TwinAt s ()   where
  type TwinAt_ s () = [(Name, Dom Type)]
  twinAt = const []

instance TwinAt s Term where twinAt = id
instance TwinAt s Type where twinAt = id

instance TwinAt s a => TwinAt s (Maybe a) where
  type TwinAt_ s (Maybe a) = Maybe (TwinAt_ s a)
  twinAt = fmap (twinAt @s)

-- -- | Various specializations of @addCtx@.
-- class AddContextHet b where
--   addContextHet  :: (MonadTCEnv m, MonadAddContext m) =>
--     ContextHet -> b -> (ContextHet -> m a) -> m a
--
-- instance AddContextHet (String, Dom TwinT) where
--   {-# INLINABLE addContextHet #-}
--   addContextHet ctx (s, dom) κ = do
--     withFreshName noRange s $ \x ->
--       addContextHet ctx (setNotInScope x, dom) κ
--
-- -- | Run under a side of a twin context
-- {-# SPECIALIZE underHet :: ContextHet -> (a -> TCM b) -> Het 'LHS a -> TCM (Het 'LHS b) #-}
-- {-# SPECIALIZE underHet :: ContextHet -> (a -> TCM b) -> Het 'RHS a -> TCM (Het 'RHS b) #-}
-- {-# SPECIALIZE underHet :: ContextHet -> (a -> TCM b) -> Het 'Compat a -> TCM (Het 'Compat b) #-}
-- underHet :: forall s m a b. (MonadAddContext m, Sing s, HetSideIsType s ~ 'True) => ContextHet -> (a -> m b) -> Het s a -> m (Het s b)
-- underHet ctx f = traverse (addContext (twinAt @s ctx) . f)
--
-- underHet' :: forall s m a het. (MonadAddContext m, Sing s, HetSideIsType s ~ 'True) =>
--              SingT het -> If het ContextHet () -> m a -> m a
-- underHet' STrue  ctx = addContext (twinAt @s ctx)
-- underHet' SFalse ()  = id
--
-- underHet_ :: forall s m a het. (MonadAddContext m, Sing s, HetSideIsType s ~ 'True, Sing het) =>
--              If_ het ContextHet () -> m a -> m a
-- underHet_ = underHet' @s @m @a @het (sing :: SingT het) . unIf
--

{-# INLINE commuteHet #-}
commuteHet :: (Coercible (f a) (f (Het s a))) => Het s (f a) -> f (Het s a)
commuteHet = coerce . unHet

-- {-# INLINE maybeInContextHet #-}
-- maybeInContextHet :: (HasOptions m) =>
--   SingT het -> If het ContextHet () ->
--     (forall het'. (Sing het', het' ~ Or het het', het' ~ Or het' het) =>
--        SingT het' -> If (Or het het') ContextHet () -> m a) -> m a
-- maybeInContextHet hetuni ctx κ = do
--   case hetuni of
--     STrue  -> κ STrue ctx
--     SFalse ->
--       heterogeneousUnification >>= \case
--         True  -> κ STrue Empty
--         False -> κ SFalse ()

class FlipHet a where
  type FlippedHet a
  type FlippedHet a = a

  flipHet :: a -> FlippedHet a

instance FlipHet (Het 'LHS a) where
  type FlippedHet (Het 'LHS a) = (Het 'RHS a)
  flipHet = coerce

instance FlipHet (Het 'RHS a) where
  type FlippedHet (Het 'RHS a) = (Het 'LHS a)
  flipHet = coerce

instance FlipHet (Het 'Both a) where
  flipHet = id

instance FlipHet TwinT where
  flipHet a@SingleT{} = a
  flipHet TwinT{twinLHS,twinRHS,twinPid,necessary,twinCompat} =
    TwinT{twinLHS=flipHet twinRHS,twinRHS=flipHet twinLHS,twinCompat,necessary,twinPid}

instance FlipHet ContextHet where
  flipHet (ContextHet ctx) = ContextHet$ fmap (fmap (fmap flipHet)) ctx

instance FlipHet Term where flipHet = id
instance FlipHet Type where flipHet = id
instance FlipHet ()   where flipHet = id

instance FlipHet a => FlipHet (CompareAs' a) where
   type FlippedHet (CompareAs' a) = CompareAs' (FlippedHet a)
   flipHet = fmap flipHet

instance (FlipHet a, FlipHet b) => FlipHet (a, b) where
  type FlippedHet (a, b) = (FlippedHet a, FlippedHet b)
  flipHet (a,b) = (flipHet a, flipHet b)

instance (FlipHet a, FlipHet b, FlipHet c) => FlipHet (a, b, c) where
  type FlippedHet (a, b, c) = (FlippedHet a, FlippedHet b, FlippedHet c)
  flipHet (a,b,c) = (flipHet a, flipHet b, flipHet c)

data HetP a = HetP (Het 'LHS a) (Het 'RHS a)
instance FlipHet (HetP a) where
  flipHet (HetP a b) = HetP (flipHet b) (flipHet a)

instance FlipHet CompareDirection where
  type FlippedHet CompareDirection = CompareDirection
  flipHet = flipCmp

-- errorInContextHet :: forall het. (Sing het) => If_ het ContextHet () -> TypeError -> TypeError
-- errorInContextHet ctx = case sing :: SingT het of
--  STrue  -> ErrorInContextHet (unIf ctx)
--  SFalse -> case ctx of If () -> id

{-# INLINE dirToCmp_ #-}
dirToCmp_ :: forall s₁ s₂ m t a c. (FlipHet t, FlippedHet t ~ t, MonadAddContext m, AreSides s₁ s₂) =>
             (Comparison -> t -> Het 'LHS a -> Het 'RHS a -> m c) ->
              CompareDirection -> t -> Het s₁ a -> Het s₂ a -> m c
dirToCmp_ κ dir a u v = go sing sing dir
  where
    go :: SingT s₁ -> SingT s₂ -> CompareDirection -> m c
    go SLHS SRHS DirGeq = flipContext$ κ CmpLeq (flipHet a) (flipHet v) (flipHet u)
    go SLHS SRHS DirEq  = κ CmpEq  a u v
    go SLHS SRHS DirLeq = κ CmpLeq a u v
    go SRHS SLHS DirGeq = κ CmpLeq a v u
    go SRHS SLHS DirEq  = flipContext$ κ CmpEq  (flipHet a) (flipHet u) (flipHet v)
    go SRHS SLHS DirLeq = flipContext$ κ CmpLeq (flipHet a) (flipHet u) (flipHet v)

drop :: Int -> ContextHet -> ContextHet
drop n = ContextHet . S.drop n . unContextHet

length :: ContextHet -> Int
length = S.length . unContextHet

(⊣::) :: [Dom (Name, Type)] -> ContextHet -> ContextHet
as ⊣:: ctx =  ContextHet ( fmap (fmap (fmap (SingleT . Het))) (S.fromList as) <> unContextHet  ctx)

(!!!) :: ContextHet -> Int -> Maybe (Dom (Name, TwinT))
ctx !!! n = contextHetToList ctx Agda.Utils.List.!!! n

-- | Switch heterogeneous context to a specific side
flipContext :: (MonadAddContext m) => m a -> m a
flipContext = updateContext IdS flipHet

