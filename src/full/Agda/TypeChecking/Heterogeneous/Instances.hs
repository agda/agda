{-# LANGUAGE CPP                        #-}
{-# LANGUAGE TypeFamilies               #-}

module Agda.TypeChecking.Heterogeneous.Instances where

import Data.Semigroup ((<>))

import Agda.TypeChecking.Heterogeneous

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Free.Lazy (Free(..), underBinder)
import Agda.TypeChecking.MetaVars.Mention
import Agda.TypeChecking.Monad.Constraints (isProblemSolved)
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Monad.Context (MonadAddContext(..), AddContext(..))

import Agda.Syntax.Internal as I
import Agda.Syntax.Internal.Generic (TermLike(..))

import Agda.Utils.Monad (allM)

import Agda.Utils.Impossible

---------------------------------------------------------------------
-- Agda.TypeChecking.Free.Lazy
---------------------------------------------------------------------

instance Free ContextHet where
  freeVars' = go
    where
      go Empty      = mempty
      go (v :⊢: vs) = freeVars' v <> underBinder (freeVars' vs)

instance Free TwinT where

---------------------------------------------------------------------
-- Instances for Agda.TypeChecking.MetaVars.Mention
---------------------------------------------------------------------

instance MentionsMeta a => MentionsMeta (Het s a) where
  mentionsMetas xs = mentionsMetas xs . unHet

instance MentionsMeta TwinT where
  mentionsMetas xs (SingleT a) = mentionsMetas xs a
  mentionsMetas xs (TwinT{twinLHS,twinRHS,twinCompat}) =
    mentionsMetas xs (twinLHS, twinRHS, twinCompat)

------------------------------------------------------------------
-- Instances for Agda.TypeChecking.Reduce
------------------------------------------------------------------
instance Instantiate TwinT where
  instantiate' = traverse instantiate'

instance Reduce TwinT where
  reduce' = traverse reduce'

instance Simplify TwinT where
  simplify' = traverse simplify'

instance Normalise TwinT where
  normalise' = traverse normalise'

instance InstantiateFull TwinT where

---------------------------------------------------------------------
-- Agda.Syntax.Internal.Generic
---------------------------------------------------------------------

instance TermLike ContextHet where
  foldTerm f = foldTerm f . contextHetToList
  traverseTermM = __IMPOSSIBLE__

instance TermLike TwinT where
  traverseTermM f = \case
    SingleT a -> SingleT <$> traverseTermM f a
    TwinT{twinPid,twinLHS=a,twinRHS=b,twinCompat=c} ->
      (\a' b' c' -> TwinT{twinPid,necessary=False,twinLHS=a',twinRHS=b',twinCompat=c'}) <$>
        traverseTermM f a <*> traverseTermM f b <*> traverseTermM f c

---------------------------------------------------------------------
-- Agda.Utils.Size
---------------------------------------------------------------------

---------------------------------------------------------------------
-- Bola extra
---------------------------------------------------------------------

class SimplifyHet a where
  type Simplified a
  unsimplifyHet :: Simplified a -> a
  simplifyHet   :: MonadConversion m => a -> (Either a (Simplified a) -> m b) -> m b

simplifyHet' :: (MonadConversion m, SimplifyHet a) => a -> (a -> m b) -> m b
simplifyHet' a κ = simplifyHet a $ \case
  Left  a' -> κ a'
  Right a' -> κ $ unsimplifyHet a'

-- instance SimplifyHet ContextHet where
--   type Simplified ContextHet = ()
--
--   unsimplifyHet () = Empty
--
--   simplifyHet Empty κ = κ (Right ())
--   simplifyHet (dt :⊢: ctx) κ =
--     simplifyHet dt $ \case
--       Right dt' -> addContext dt' $ simplifyHet ctx κ
--       Left  dt' -> κ$ Left$ (dt' :⊢: ctx)

instance SimplifyHet TwinT where
  type Simplified TwinT = Type

  unsimplifyHet = SingleT . Het @'Both

  simplifyHet (SingleT a) κ = κ$ Right $ unHet @'Both a
  simplifyHet a@(TwinT{twinPid,twinCompat}) κ =
    allM twinPid isProblemSolved >>= \case
      True  -> κ$ Right $ unHet @'Compat twinCompat
      False -> κ$ Left  a

-- instance SimplifyHet a => SimplifyHet (WithHet a) where
--   type Simplified (WithHet a) = Simplified a
--
--   unsimplifyHet = WithHet Empty . unsimplifyHet
--
--   simplifyHet (WithHet ctx a) κ = simplifyHet ctx $ \case
--     Right () -> simplifyHet a $ \case
--       Left  a' -> κ$ Left$ WithHet Empty a'
--       Right a' -> κ$ Right$ a'
--     Left ctx'  -> κ$ Left$ WithHet ctx' a

-- instance SimplifyHet a => SimplifyHet (Name, a) where

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

