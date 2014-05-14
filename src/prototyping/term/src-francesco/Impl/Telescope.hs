{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
module Impl.Telescope
    ( Telescope
    , ClosedTelescope
    , telescopeEmpty
    , telescopeExtend
    ) where

import           Control.Monad                    (liftM)
import           Data.Foldable                    (Foldable)
import           Data.Traversable                 (Traversable)
import           Bound
import           Data.Void                        (Void)

import           Syntax.Abstract                  (Name)
import           Syntax.Abstract.Pretty           ()
import           Impl.Term

-- Telescope
------------------------------------------------------------------------

-- | A 'Telescope' is a series of binding with some content at the end.
-- Each binding ranges over the rest of the telescope.
data Telescope t v
    = EmptyTel (t v)
    | t v :> Telescope t (TermVar v)
    deriving (Functor, Foldable, Traversable)

instance Bound Telescope where
    EmptyTel t  >>>= f = EmptyTel (t >>= f)
    (t :> tele) >>>= f = (t >>= f) :> (tele >>>= extended)
      where
        extended (B v) = return (B v)
        extended (F v) = liftM F (f v)

type ClosedTelescope t = Telescope t Void

telescopeEmpty :: t v -> Telescope t v
telescopeEmpty t = EmptyTel t

telescopeExtend :: Monad t => t Name -> Name -> Telescope t Name -> Telescope t Name
telescopeExtend t1 n tele = t1 :> (tele >>>= return . abstractTele)
  where
    abstractTele :: Name -> TermVar Name
    abstractTele n' = if n == n' then boundTermVar n else F n'

telescopeClose :: Monad t => Telescope t Name -> ClosedTelescope t
telescopeClose tele = tele >>>= return . killNames
  where
    killNames n = error $ "telescopeClose: out of bound name " ++ show n

-- substs :: forall t0 v. Telescope t0 v -> [t0 v] -> t0 v
-- substs = undefined              -- TODO reverse here
--   where
--     go :: (t v -> t0 v) -> Telescope t v -> [t v] -> t0 v
--     go f (EmptyTel t) []           = f t
--     go _ (EmptyTel _) (_ : _)      = error "Telescope.substs: too many arguments"
--     go f (_ :> _)     []           = error "Telescope.substs: too few arguments"
--     go f (_ :> tele)  (arg : args) =
--         go undefined tele (map (abstract1 args)
