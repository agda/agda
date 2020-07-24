{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE CPP                        #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE ViewPatterns               #-}
{-# LANGUAGE TypeFamilies               #-}

module Agda.TypeChecking.Heterogeneous where

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

import {-# SOURCE #-} Agda.TypeChecking.Monad.Base
import {-# SOURCE #-} Agda.TypeChecking.Conversion
import {-# SOURCE #-} Agda.TypeChecking.Monad.Context (MonadAddContext(..), AddContext(..))
import Agda.TypeChecking.Monad.Constraints (isProblemSolved)

import Agda.Utils.Dependent
import Agda.Utils.Monad
import Agda.Utils.Pretty
import Agda.Utils.Size

import Agda.Utils.Impossible

----------------------------------------------------------------------
-- * Data structure for a twin type
----------------------------------------------------------------------

data TwinT'' b a  =
    SingleT { unSingleT :: Het 'Both a }
  | TwinT { twinPid    :: [ProblemId]      -- ^ Unification problem which is sufficient
                                           --   for LHS and RHS to be equal
          , necessary  :: b                -- ^ Whether solving twinPid is necessary,
                                           --   not only sufficient.
          , twinLHS    :: Het 'LHS a       -- ^ Left hand side of the twin
          , twinRHS    :: Het 'RHS a       -- ^ Right hand side of the twin
          , twinCompat :: Het 'Compat a    -- ^ A term which can be used instead of the
                                      --   twin for backwards compatibility
                                      --   purposes.
          }
   deriving (Foldable, Traversable)

deriving instance (Data a, Data b) => Data (TwinT'' a b)
deriving instance (Show a, Show b) => Show (TwinT'' a b)
deriving instance Functor (TwinT'' b)

type TwinT' = TwinT'' Bool

type TwinT = TwinT' Type

data WithHet' c a = WithHet c a
type WithHet a = WithHet' ContextHet a

type family HetSideIsType (s :: HetSide) :: Bool where
  HetSideIsType 'LHS    = 'True
  HetSideIsType 'RHS    = 'True
  HetSideIsType 'Compat = 'True
  HetSideIsType 'Both   = 'True
  HetSideIsType 'Whole  = 'False

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

data HetSide = LHS | RHS | Compat | Whole | Both
data instance SingT (a :: HetSide) where
  SLHS    :: SingT 'LHS
  SRHS    :: SingT 'RHS
  SCompat :: SingT 'Compat
  SWhole  :: SingT 'Whole
  SBoth   :: SingT 'Both
instance Sing 'LHS    where sing = SLHS
instance Sing 'RHS    where sing = SRHS
instance Sing 'Both   where sing = SBoth
instance Sing 'Compat where sing = SCompat
instance Sing 'Whole  where sing = SWhole

newtype Het (side :: HetSide) t = Het { unHet :: t }
  deriving (Foldable, Traversable, Pretty)

deriving instance (Typeable side, Data t) => Data (Het side t)
deriving instance Show t => Show (Het side t)
deriving instance Functor (Het side)

instance Applicative (Het s) where
  pure = Het
  mf <*> ma = mf >>= (\f -> ma >>= (\a -> pure (f a)))
instance Monad (Het s) where
  Het a >>= f = f a

instance TermLike t => TermLike (Het a t) where

-- | The context is in left-to-right order
newtype ContextHet = ContextHet { unContextHet :: Seq (Name, Dom TwinT) }
  deriving (Data, Show)

pattern Empty :: ContextHet
pattern Empty                    = ContextHet S.Empty
pattern (:<|) :: (Name, Dom TwinT) -> ContextHet -> ContextHet
pattern a :<| ctx <- ContextHet (a S.:<| (ContextHet -> ctx))
  where a :<| ctx =  ContextHet (a S.:<|  unContextHet  ctx )
pattern (:|>) :: ContextHet -> (Name, Dom TwinT) -> ContextHet
pattern ctx :|> a <- ContextHet ((ContextHet -> ctx) S.:|> a)
  where ctx :|> a =  ContextHet ( unContextHet  ctx  S.:|> a)
{-# COMPLETE Empty, (:<|) #-}
{-# COMPLETE Empty, (:|>) #-}


instance AddContextHet (Name, Dom TwinT) where
  {-# INLINABLE addContextHet #-}
  addContextHet ctx p κ = κ$ ctx :|> p

class TwinAt (s :: HetSide) a where
  type TwinAt_ s a
  type TwinAt_ s a = a
  twinAt :: a -> TwinAt_ s a

instance (Sing s, HetSideIsType s ~ 'True) => TwinAt s ContextHet where
  type TwinAt_ s ContextHet = [(Name, Dom Type)]
  twinAt = fmap (fmap (fmap (twinAt @s))) . toList . unContextHet

--instance TwinAt s a => TwinAt s (CompareAs' a) where
--  type TwinAt_ s (CompareAs' a) = CompareAs' (TwinAt_ s a)
--  twinAt = fmap (twinAt @s)

instance (Sing s, HetSideIsType s ~ 'True) => TwinAt s TwinT where
  type TwinAt_ s TwinT = Type
  {-# INLINE twinAt #-}
  twinAt (SingleT a) = unHet @'Both a
  twinAt TwinT{twinLHS,twinRHS,twinCompat} = case (sing :: SingT s) of
    SLHS    -> unHet @s $ twinLHS
    SBoth   -> unHet @'LHS $ twinLHS
    SRHS    -> unHet @s $ twinRHS
    SCompat -> unHet @s $ twinCompat

instance TwinAt s ()   where
  type TwinAt_ s () = [(Name, Dom Type)]
  twinAt = const []

instance TwinAt s Term where twinAt = id
instance TwinAt s Type where twinAt = id
instance TwinAt s (Het s a) where
  type TwinAt_ s (Het s a) = a
  twinAt = coerce

instance TwinAt 'Compat (Het 'LHS a) where
  type TwinAt_ 'Compat (Het 'LHS a) = a
  twinAt = coerce

instance TwinAt 'Compat (Het 'RHS a) where
  type TwinAt_ 'Compat (Het 'RHS a) = a
  twinAt = coerce

instance (TwinAt s a, TwinAt s b, Sing het, TwinAt_ s a ~ TwinAt_ s b) => TwinAt s (If_ het a b) where
  type TwinAt_ s (If_ het a b) = TwinAt_ s a
  twinAt = case sing :: SingT het of
    STrue  -> twinAt @s . unIf
    SFalse -> twinAt @s . unIf

-- | Various specializations of @addCtx@.
class AddContextHet b where
  addContextHet  :: (MonadTCEnv m, MonadAddContext m) =>
    ContextHet -> b -> (ContextHet -> m a) -> m a

instance AddContextHet (String, Dom TwinT) where
  {-# INLINABLE addContextHet #-}
  addContextHet ctx (s, dom) κ = do
    withFreshName noRange s $ \x ->
      addContextHet ctx (setNotInScope x, dom) κ

-- | Run under a side of a twin context
{-# SPECIALIZE underHet :: ContextHet -> (a -> TCM b) -> Het 'LHS a -> TCM (Het 'LHS b) #-}
{-# SPECIALIZE underHet :: ContextHet -> (a -> TCM b) -> Het 'RHS a -> TCM (Het 'RHS b) #-}
{-# SPECIALIZE underHet :: ContextHet -> (a -> TCM b) -> Het 'Compat a -> TCM (Het 'Compat b) #-}
underHet :: forall s m a b. (MonadAddContext m, Sing s, HetSideIsType s ~ 'True) => ContextHet -> (a -> m b) -> Het s a -> m (Het s b)
underHet ctx f = traverse (addContext (twinAt @s ctx) . f)

underHet' :: forall s m a het. (MonadAddContext m, Sing s, HetSideIsType s ~ 'True) =>
             SingT het -> If het ContextHet () -> m a -> m a
underHet' STrue  ctx = addContext (twinAt @s ctx)
underHet' SFalse ()  = id

underHet_ :: forall s m a het. (MonadAddContext m, Sing s, HetSideIsType s ~ 'True, Sing het) =>
             If_ het ContextHet () -> m a -> m a
underHet_ = underHet' @s @m @a @het (sing :: SingT het) . unIf


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

class SimplifyHet a where
  type Simplified a
  unsimplifyHet :: Simplified a -> a
  simplifyHet   :: MonadConversion m => a -> (Either a (Simplified a) -> m b) -> m b

simplifyHet' :: (MonadConversion m, SimplifyHet a) => a -> (a -> m b) -> m b
simplifyHet' a κ = simplifyHet a $ \case
  Left  a' -> κ a'
  Right a' -> κ $ unsimplifyHet a'

instance SimplifyHet ContextHet where
  type Simplified ContextHet = ()

  unsimplifyHet () = Empty

  simplifyHet Empty κ = κ (Right ())
  simplifyHet ((name, dt) :<| ctx) κ =
    simplifyHet dt $ \case
      Right dt' -> addContext (name, dt') $ simplifyHet ctx κ
      Left  dt' -> κ$ Left$ ((name, dt') :<| ctx)

instance SimplifyHet TwinT where
  type Simplified TwinT = Type

  unsimplifyHet = SingleT . Het @'Both

  simplifyHet (SingleT a) κ = κ$ Right $ unHet @'Both a
  simplifyHet a@(TwinT{twinPid,twinCompat}) κ =
    allM twinPid isProblemSolved >>= \case
      True  -> κ$ Right $ unHet @'Compat twinCompat
      False -> κ$ Left  a

instance SimplifyHet a => SimplifyHet (WithHet a) where
  type Simplified (WithHet a) = Simplified a

  unsimplifyHet = WithHet Empty . unsimplifyHet

  simplifyHet (WithHet ctx a) κ = simplifyHet ctx $ \case
    Right () -> simplifyHet a $ \case
      Left  a' -> κ$ Left$ WithHet Empty a'
      Right a' -> κ$ Right$ a'
    Left ctx'  -> κ$ Left$ WithHet ctx' a

instance SimplifyHet a => SimplifyHet (Dom a) where
  type Simplified (Dom a) = Dom (Simplified a)

  unsimplifyHet = fmap unsimplifyHet
  simplifyHet a κ = simplifyHet (unDom a) $ \case
    Left  a' -> κ$ Left$  a{unDom=a'}
    Right a' -> κ$ Right$ a{unDom=a'}

-- instance SimplifyHet a => SimplifyHet (CompareAs' a) where
--   type Simplified (CompareAs' a) = CompareAs' (Simplified a)
--
--   unsimplifyHet = fmap unsimplifyHet
--   simplifyHet AsTypes κ     = κ (Right AsTypes)
--   simplifyHet AsSizes κ     = κ (Right AsSizes)
--   simplifyHet (AsTermsOf a) κ = simplifyHet a $ \case
--     Right a' -> κ$ Right$ AsTermsOf a'
--     Left  a' -> κ$ Left$  AsTermsOf a'

instance SimplifyHet a => SimplifyHet (Het side a) where
  type Simplified (Het side a) = Simplified a

  unsimplifyHet = Het . unsimplifyHet

  simplifyHet (Het a) κ = simplifyHet a $ \case
    Right a' -> κ$ Right a'
    Left  a' -> κ$ Left$ Het a'

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
