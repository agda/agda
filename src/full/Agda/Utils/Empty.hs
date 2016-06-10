{-# LANGUAGE CPP #-}

-- | An empty type with some useful instances.
module Agda.Utils.Empty where

import Agda.Utils.Impossible

#include "undefined.h"

data Empty

instance Eq Empty where
  _ == _ = True

instance Ord Empty where
  compare _ _ = EQ

instance Show Empty where
  showsPrec p _ = showParen (p > 9) $ showString "error \"Agda.Utils.Empty.Empty\""

absurd :: Empty -> a
absurd e = seq e __IMPOSSIBLE__

