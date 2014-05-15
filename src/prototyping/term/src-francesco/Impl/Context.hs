{-# LANGUAGE GADTs #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TupleSections #-}
module Impl.Context
    ( -- * 'Context'
      Context(..)
    , ClosedContext
    , empty
    , singleton
    , lookup
    , app
    , pi
    , length
    , elemIndex
    , (++)
    , weaken

      -- * 'Telescope'
    , Telescope
    , ClosedTelescope
    , telescope
    , instantiate
    ) where

import           Prelude                          hiding (pi, length, lookup, (++))

import           Bound                            hiding (instantiate)
import           Data.Void                        (Void, absurd)
import           Control.Arrow                    ((***))
import           Data.Foldable                    (Foldable(foldMap))
import           Data.Traversable                 (Traversable, sequenceA)
import           Control.Monad                    (liftM)
import           Data.Monoid                      (mempty, (<>))
import           Control.Applicative              ((<$>), (<*>))

import           Syntax.Abstract                  (Name)
import           Impl.Term
import           Term

-- Context
------------------------------------------------------------------------

-- | A 'Context' is the same as a 'Telescope', but inside out: the last
-- binding we encounter ranges over all the precedent ones.
data Context v0 t v where
    Empty :: Context v0 t v0
    (:<)  :: Context v0 t v -> (Name, t v) -> Context v0 t (TermVar v)

type ClosedContext = Context Void

empty :: Context v0 t v0
empty = Empty

singleton :: Name -> t v0 -> Context v0 t (TermVar v0)
singleton name t = Empty :< (name, t)

lookup :: Name -> Context v0 Type v -> Maybe (v, Type v)
lookup n ctx0 = go ctx0
  where
    -- Helper function so that we have the proof of equality when
    -- pattern matching the variable.
    go :: Context v0 Type v -> Maybe (v, Type v)
    go Empty                = Nothing
    go (ctx :< (n', type_)) = if n == n'
                              then Just (boundTermVar n, fmap F type_)
                              else fmap (F *** fmap F) (go ctx)

-- | Applies a 'Term' to all the variables in the context.  The
-- variables are applied from left to right.
app :: Term v -> Context v0 Type v -> Term v
app t ctx0 = eliminate t $ map (Apply . return) $ reverse $ go ctx0
  where
    go :: Context v0 Type v -> [v]
    go Empty                  = []
    go (ctx :< (name, _type)) = boundTermVar name : map F (go ctx)

-- | Creates a 'Pi' type containing all the types in the 'Context' and
-- terminating with the provided 'Type'.
pi :: Context v0 Type v -> Type v -> Type v0
pi Empty                t = t
pi (ctx :< (_n, type_)) t = pi ctx (Pi type_ (toScope t))

length :: Context v0 t v -> Int
length Empty      = 0
length (ctx :< _) = 1 + length ctx

-- | Gets the index of a variable *from the left*.  0-indexed.  So the
-- rightmost thing will have index @length 'Context' - 1@, and the leftmost
-- thing will have index @0@.  Also returns the name at that index.
elemIndex :: v -> ClosedContext t v -> Named Int
elemIndex v0 ctx0 = fmap (length ctx0 -) $ go ctx0 v0
  where
    go :: ClosedContext t v -> v -> Named Int
    go Empty v = absurd v
    go (_ctx :< (n, _type)) (B _) = named n 1
    go ( ctx :< _         ) (F v) = fmap (+ 1) $ go ctx v

(++) :: Context v0 t v1 -> Context v1 t v2 -> Context v0 t v2
ctx1 ++ Empty               = ctx1
ctx1 ++ (ctx2 :< namedType) = (ctx1 ++ ctx2) :< namedType

weaken :: Context v0 t v -> v0 -> v
weaken Empty      v = v
weaken (ctx :< _) v = F (weaken ctx v)

-- Telescope
------------------------------------------------------------------------

data Telescope t v0 = forall v. Telescope (Context v0 t v) (t v)

type ClosedTelescope t = Telescope t Void

telescope :: Context v0 t v -> t v -> Telescope t v0
telescope = Telescope

instance Functor t => Functor (Telescope t) where
    fmap f tel = fromConcreteTele (fmap f (toConcreteTele tel))

instance Foldable t => Foldable (Telescope t) where
    foldMap f tel = foldMap f (toConcreteTele tel)

instance Traversable t => Traversable (Telescope t) where
    sequenceA = fmap fromConcreteTele . sequenceA . toConcreteTele

instance Bound Telescope where
    tel >>>= f = fromConcreteTele (toConcreteTele tel >>>= f)

instantiate :: Monad t => Telescope t v0 -> [t v0] -> t v0
instantiate = go . toConcreteTele
  where
    go :: Monad t => ConcreteTele t v -> [t v] -> t v
    go (TEmpty t) []           = t
    go (TEmpty _) (_ : _)      = error "Impl.Context.instantiate: too many arguments"
    go (_ :> _)   []           = error "Impl.Context.instantiate: too few arguments"
    go (_ :> tel) (arg : args) = go (tel >>>= instArg) args
      where
        instArg (B _) = arg
        instArg (F v) = return v

-- Concrete telescopes
----------------------

-- We use this datatype, isomorphic to 'Telescope', to easily derive
-- instances for 'Telescope'.

-- TODO define instances and functions directly avoiding traversals.

data ConcreteTele t v
    = TEmpty (t v)
    | (Name, t v) :> ConcreteTele t (TermVar v)
    deriving (Functor)

instance Foldable t => Foldable (ConcreteTele t) where
    foldMap f (TEmpty t)          = foldMap f t
    foldMap f ((_, type_) :> tel) = foldMap f type_ <> foldMap extend tel
      where
        extend (B _) = mempty
        extend (F v) = f v

instance Traversable t => Traversable (ConcreteTele t) where
    sequenceA (TEmpty t)          = TEmpty <$> sequenceA t
    sequenceA ((n, type_) :> tel) =
        (:>) <$> ((n ,) <$> sequenceA type_) <*> sequenceA (fmap sequenceA tel)

instance Bound ConcreteTele where
    (TEmpty t)          >>>= f = TEmpty (t >>= f)
    ((n, type_) :> tel) >>>= f = (n, type_ >>= f) :> (tel >>>= extend)
      where
        extend (B v) = return (B v)
        extend (F v) = liftM F (f v)

toConcreteTele :: Telescope t v -> ConcreteTele t v
toConcreteTele (Telescope ctx0 t) = go ctx0 (TEmpty t)
  where
    go :: Context v0 t v -> ConcreteTele t v -> ConcreteTele t v0
    go Empty          tel = tel
    go (ctx :< type_) tel = go ctx (type_ :> tel)

fromConcreteTele :: ConcreteTele t v -> Telescope t v
fromConcreteTele tel0 = go tel0 Empty
  where
    go :: ConcreteTele t v -> Context v0 t v -> Telescope t v0
    go (TEmpty t)     ctx = Telescope ctx t
    go (type_ :> tel) ctx = go tel (ctx :< type_)
