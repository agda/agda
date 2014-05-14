{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
module Impl.Telescope
    ( Telescope
    , ClosedTelescope
    , instantiate
    ) where

import           Control.Monad                    (liftM)
import           Data.Foldable                    (Foldable)
import           Data.Traversable                 (Traversable)
import           Bound                            (Bound((>>>=)), Var(B, F))
import           Data.Void                        (Void)

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

-- empty :: t v -> Telescope t v
-- empty t = EmptyTel t

-- extend :: Monad t => t Name -> Name -> Telescope t Name -> Telescope t Name
-- extend t1 n tele = t1 :> (tele >>>= return . abstractTele)
--   where
--     abstractTele :: Name -> TermVar Name
--     abstractTele n' = if n == n' then boundTermVar n else F n'

-- close :: Monad t => Telescope t Name -> ClosedTelescope t
-- close tele = tele >>>= return . killNames
--   where
--     killNames n = error $ "telescopeClose: out of bound name " ++ show n

instantiate :: Monad t => Telescope t v -> [t v] -> t v
instantiate (EmptyTel t) [] =
    t
instantiate (EmptyTel _) (_ : _) =
    error "Telescope.instantiate: too many args"
instantiate (_ :> _) [] =
    error "Telescope.instantiate: too few args"
instantiate (_ :> tele) (arg : args) =
    instantiate (tele >>>= substArg) args
  where
    substArg (B _) = arg
    substArg (F v) = return v
