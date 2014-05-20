module Types.Telescope
    ( -- * 'Tel'
      Tel(..)
    , ClosedTel
    , tel
    , unTel
    , idTel
    , proxyTel
    , substs
    , instantiate
      -- ** 'Tel' types
    , Proxy2(..)
    , Id2(..)
    , ProxyTel
    , ClosedProxyTel
    , IdTel
    , ClosedIdTel
    ) where

import           Prelude                          hiding (pi, length, lookup, (++))

import           Bound                            hiding (instantiate)
import           Data.Void                        (Void)
import           Data.Foldable                    (Foldable(foldMap))
import           Data.Traversable                 (Traversable, sequenceA)
import           Control.Monad                    (liftM)
import           Data.Monoid                      (mempty, (<>))
import           Control.Applicative              ((<$>), (<*>), pure)

import           Syntax.Abstract                  (Name)
import           Types.Term
import qualified Types.Context                    as Ctx

-- Tel
------------------------------------------------------------------------

data Tel t f v
    = Empty (t f v)
    | Cons (Name, f v) (Tel t f (TermVar v))
    deriving (Functor)

type ClosedTel t f = Tel t f Void

substs :: (Monad f) => IdTel f v0 -> [f v0] -> f v0
substs (Empty t)     []           = unId2 t
substs (Empty _)     (_ : _)      = error "Types.Telescope.instantiate: too many arguments"
substs (Cons _ _)    []           = error "Types.Telescope.instantiate: too few arguments"
substs (Cons _ tel') (arg : args) = substs (tel' >>>= instArg) args
  where
    instArg (B _) = arg
    instArg (F v) = return v

instantiate :: (Monad f, Bound t) => Tel t f (TermVar v) -> f v -> Tel t f v
instantiate tel' t = tel' >>>= inst
  where
    inst (B _) = t
    inst (F v) = return v

-- Useful types
---------------

data Proxy2 (f :: * -> *) v = Proxy2

instance Functor (Proxy2 f) where
     fmap _ Proxy2 = Proxy2

instance Foldable (Proxy2 f) where
     foldMap _ Proxy2 = mempty

instance Traversable (Proxy2 f) where
     sequenceA Proxy2 = pure Proxy2

instance Bound Proxy2 where
     Proxy2 >>>= _ = Proxy2

newtype Id2 f v = Id2 {unId2 :: f v}
     deriving (Functor, Foldable, Traversable)

instance Bound Id2 where
     Id2 t >>>= f = Id2 (t >>= f)

type IdTel    = Tel Id2
type ProxyTel = Tel Proxy2

type ClosedIdTel t    = IdTel t Void
type ClosedProxyTel t = ProxyTel t Void

-- Instances
----------------------

instance (Foldable f, Foldable (t f)) => Foldable (Tel t f) where
    foldMap f (Empty t)              = foldMap f t
    foldMap f (Cons (_, type_) tel') = foldMap f type_ <> foldMap f' tel'
      where
        f' (B _) = mempty
        f' (F v) = f v

instance (Traversable f, Traversable (t f)) => Traversable (Tel t f) where
    sequenceA (Empty t)              = Empty <$> sequenceA t
    sequenceA (Cons (n, type_) tel') = Cons <$> ((n ,) <$> sequenceA type_)
                                            <*> sequenceA (fmap sequenceA tel')

instance (Bound t) => Bound (Tel t) where
    (Empty t)              >>>= f = Empty (t >>>= f)
    (Cons (n, type_) tel') >>>= f = Cons (n, type_ >>= f) (tel' >>>= f')
      where
        f' (B v) = return (B v)
        f' (F v) = liftM F (f v)

-- To/from Ctx
--------------

tel :: Ctx.Ctx v0 f v -> t f v -> Tel t f v0
tel ctx0 t = go ctx0 (Empty t)
  where
    go :: Ctx.Ctx v0 f v -> Tel t f v -> Tel t f v0
    go Ctx.Empty            tel' = tel'
    go (Ctx.Snoc ctx type_) tel' = go ctx (Cons type_ tel')

idTel :: Ctx.Ctx v0 f v -> f v -> IdTel f v0
idTel ctx t = tel ctx (Id2 t)

proxyTel :: Ctx.Ctx v0 f v -> ProxyTel f v0
proxyTel ctx = tel ctx Proxy2

unTel :: forall t f v0 a.
         Tel t f v0
      -> (forall v. Ctx.Ctx v0 f v -> t f v -> a)
      -> a
unTel tel0 f = go tel0 Ctx.Empty
  where
    go :: Tel t f v -> Ctx.Ctx v0 f v -> a
    go (Empty t)         ctx = f ctx t
    go (Cons type_ tel') ctx = go tel' (Ctx.Snoc ctx type_)
