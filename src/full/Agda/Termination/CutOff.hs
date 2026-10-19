{-# OPTIONS_GHC -Wunused-imports #-}

-- | Defines 'CutOff' type which is used in "Agda.Interaction.Options".
--   This module's purpose is to eliminate the dependency of
--   "Agda.TypeChecking.Monad.Base" on the termination checker and
--   everything it imports.

module Agda.Termination.CutOff
  ( CutOff(CutOff, DontCutOff)
  , defaultCutOff
  ) where

import Control.DeepSeq

import Agda.Utils.Impossible (__IMPOSSIBLE__)

-- | Cut off structural order comparison at some depth in termination checker?

data CutOff
  = CutOff !Int -- ^ @c >= 0@ means: record decrease up to including @c+1@.
  | DontCutOff
  deriving (Eq, Ord)

-- | Numeric literals and addition for 'CutOff'.

instance Num CutOff where
  fromInteger n
    | n >= 0    = CutOff (fromInteger n)
    | otherwise = __IMPOSSIBLE__

  DontCutOff + _          = DontCutOff
  _          + DontCutOff = DontCutOff
  CutOff m   + CutOff n   = CutOff (m + n)

  _ * _    = __IMPOSSIBLE__
  abs _    = __IMPOSSIBLE__
  signum _ = __IMPOSSIBLE__
  negate _ = __IMPOSSIBLE__

instance Show CutOff where
  show (CutOff k) = show k
  show DontCutOff = "∞"

instance NFData CutOff where
  rnf (CutOff _) = ()
  rnf DontCutOff = ()

-- | The default termination depth.

defaultCutOff :: CutOff
defaultCutOff = CutOff 2 -- termination-depth=3
