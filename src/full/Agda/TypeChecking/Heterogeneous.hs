{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE CPP                        #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE ViewPatterns               #-}
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

import Agda.Utils.Dependent
import Agda.Utils.Monad
import Agda.Utils.Pretty

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
             <> "["
             <> pretty twinPid
             <> (if necessary then "" else "*")
             <> "]"
             <> pretty b

instance (Sing het, Pretty a, Pretty b) => Pretty (If_ het a b) where
  pretty (If a) = case sing :: SingT het of
    STrue  -> pretty a
    SFalse -> pretty a


instance TermLike t => TermLike (Het a t) where



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
instance (TwinAt s a, TwinAt s b, Sing het, TwinAt_ s a ~ TwinAt_ s b) => TwinAt s (If_ het a b) where
  type TwinAt_ s (If_ het a b) = TwinAt_ s a
  twinAt = case sing :: SingT het of
    STrue  -> twinAt @s . unIf
    SFalse -> twinAt @s . unIf

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

type IfHet_ het side a = If  het (Het side a) a
type IfHet het side a =  If_ het (Het side a) a
newtype If_ het a b = If { unIf :: If het a b }
pattern IfHet :: forall s het a. IfHet_ het s a -> IfHet het s a
pattern IfHet a = If a

{-# INLINE mkIfHet #-}
mkIfHet :: forall s het a. (Sing het) => IfHet_ het s a -> IfHet het s a
mkIfHet = If

{-# INLINE mkIfHet_ #-}
mkIfHet_ :: forall s het a. (Sing het) => Het s a -> IfHet het s a
mkIfHet_ = mkHet_ . unHet

{-# INLINE mkHet_ #-}
mkHet_ :: forall s het a. (Sing het) => a -> IfHet het s a
mkHet_ = case sing :: SingT het of
  STrue -> If . Het
  SFalse -> If . id

{-# INLINE rHet_ #-}
rHet_ :: forall s het het' a. (Sing het, Sing het') => IfHet het' s a -> IfHet het s a
rHet_ = mkHet_ . unHet_

{-# INLINE unHet_ #-}
unHet_ :: forall s het a. (Sing het) => IfHet het s a -> a
unHet_ = case sing :: SingT het of
  STrue  -> unHet . unIf
  SFalse -> id . unIf

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

-- instance FlipHet a => FlipHet (CompareAs' a) where
--   type FlippedHet (CompareAs' a) = CompareAs' (FlippedHet a)
--   flipHet = fmap flipHet

instance (Sing het, FlipHet a, FlipHet b) => FlipHet (If_ het a b) where
  type FlippedHet (If_ het a b) = If_ het (FlippedHet a) (FlippedHet b)
  flipHet = case sing :: SingT het of
    STrue  -> If . flipHet . unIf
    SFalse -> If . flipHet . unIf

instance (FlipHet a, FlipHet b) => FlipHet (a, b) where
  type FlippedHet (a, b) = (FlippedHet a, FlippedHet b)
  flipHet (a,b) = (flipHet a, flipHet b)

instance (FlipHet a, FlipHet b, FlipHet c) => FlipHet (a, b, c) where
  type FlippedHet (a, b, c) = (FlippedHet a, FlippedHet b, FlippedHet c)
  flipHet (a,b,c) = (flipHet a, flipHet b, flipHet c)

data HetP a = HetP (Het 'LHS a) (Het 'RHS a)
instance FlipHet (HetP a) where
  flipHet (HetP a b) = HetP (flipHet b) (flipHet a)

-- errorInContextHet :: forall het. (Sing het) => If_ het ContextHet () -> TypeError -> TypeError
-- errorInContextHet ctx = case sing :: SingT het of
--  STrue  -> ErrorInContextHet (unIf ctx)
--  SFalse -> case ctx of If () -> id

dirToCmp_ :: (FlipHet a, FlippedHet a ~ a) => CompareDirection -> a -> (Comparison -> a -> c) -> c
dirToCmp_ DirGeq a κ = κ CmpLeq (flipHet a)
dirToCmp_ DirEq  a κ = κ CmpEq  a
dirToCmp_ DirLeq a κ = κ CmpLeq a

drop :: Int -> ContextHet -> ContextHet
drop n = ContextHet . S.drop n . unContextHet

length :: ContextHet -> Int
length = S.length . unContextHet

(⊣::) :: [Dom (Name, Type)] -> ContextHet -> ContextHet
as ⊣:: ctx =  ContextHet ( fmap (fmap (fmap (SingleT . Het))) (S.fromList as) <> unContextHet  ctx)
