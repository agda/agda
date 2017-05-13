{-# LANGUAGE CPP                #-}
{-# LANGUAGE DeriveDataTypeable #-}

#if __GLASGOW_HASKELL__ <= 708
{-# LANGUAGE DeriveDataTypeable #-}
#endif

-- | An empty type with some useful instances.
module Agda.Utils.Empty where

import Data.Data (Data)

#if __GLASGOW_HASKELL__ <= 708
import Data.Typeable ( Typeable )
#endif

import Agda.Utils.Impossible

#include "undefined.h"

data Empty
#if __GLASGOW_HASKELL__ <= 708
  deriving Typeable
#endif
deriving instance Data Empty

instance Eq Empty where
  _ == _ = True

instance Ord Empty where
  compare _ _ = EQ

instance Show Empty where
  showsPrec p _ = showParen (p > 9) $ showString "error \"Agda.Utils.Empty.Empty\""

absurd :: Empty -> a
absurd e = seq e __IMPOSSIBLE__

