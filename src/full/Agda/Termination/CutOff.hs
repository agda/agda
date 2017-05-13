{-# LANGUAGE CPP #-}

#if __GLASGOW_HASKELL__ <= 708
{-# LANGUAGE DeriveDataTypeable #-}
#endif

-- | Defines 'CutOff' type which is used in "Agda.Interaction.Options".
--   This module's purpose is to eliminate the dependency of
--   "Agda.TypeChecking.Monad.Base" on the termination checker and
--   everything it imports.

module Agda.Termination.CutOff where

#if __GLASGOW_HASKELL__ <= 708
import Data.Typeable ( Typeable )
#endif

-- | Cut off structural order comparison at some depth in termination checker?

data CutOff
  = CutOff Int -- ^ @c >= 0@ means: record decrease up to including @c+1@.
  | DontCutOff
  deriving ( Eq
           , Ord
#if __GLASGOW_HASKELL__ <= 708
           , Typeable
#endif
           )

instance Show CutOff where
  show (CutOff k) = show k
  show DontCutOff = "∞"

-- That's it!
