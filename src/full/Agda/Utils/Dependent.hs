-- | This module implements a poor man’s version of the singletons package.
--   We do this instead of importing the 'singletons' package in order
--   to avoid the dependency, and because the automation provided by this
--   packages relies on Template Haskell, which complicates compilation.
--
--   https://cs.brynmawr.edu/~rae/papers/2012/singletons/paper.pdf
--   https://hackage.haskell.org/package/singletons-2.7/docs/Data-Singletons.html

{-# LANGUAGE KindSignatures  #-}
{-# LANGUAGE GADTs           #-}
{-# LANGUAGE PolyKinds       #-}
{-# LANGUAGE TypeFamilies    #-}
module Agda.Utils.Dependent where

import qualified Data.Kind as Hs

data family SingT :: k -> Hs.Type

class Sing (a :: k) where
  sing :: SingT a

data instance SingT (b :: Bool) where
  STrue  :: SingT 'True
  SFalse :: SingT 'False

instance Sing 'True  where sing = STrue
instance Sing 'False where sing = SFalse

type family If (cond :: Bool) (a :: k) (b :: k) :: k where
  If 'True  a b = a
  If 'False a b = b

type family And (a :: Bool) (b :: Bool) :: Bool where
  And 'True  a = a
  And 'False a = 'False

type family Or (a :: Bool) (b :: Bool) :: Bool where
  Or 'True  a = 'True
  Or 'False a = a
