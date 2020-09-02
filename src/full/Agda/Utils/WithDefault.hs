{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}

-- | Potentially uninitialised Booleans

-- The initial motivation for this small library is to be able to distinguish
-- between a boolean option with a default value and an option which has been
-- set to what happens to be the default value. In one case the default can be
-- overriden (e.g. --cubical implies --without-K) while in the other case the
-- user has made a mistake which they need to fix.

module Agda.Utils.WithDefault
  ( WithDefault (Default, Value)
  , setDefault
  , collapseDefault
  ) where

import Agda.Utils.TypeLits (KnownVal, knownVal)

-- We don't want to have to remember for each flag whether its default value
-- is True or False. So we bake it into the representation: the flag's type
-- will mention its default value as a phantom parameter.

data WithDefault (b :: t) = Default | Value t
  deriving (Eq, Show)

-- The main mode of operation of these flags, apart from setting them explicitly,
-- is to toggle them one way or the other if they hadn't been already.

setDefault :: t -> WithDefault (b :: t) -> WithDefault b
setDefault b = \case
  Default -> Value b
  t -> t

-- Provided that the default value is a known boolean (in practice we only use
-- True or False), we can collapse a potentially uninitialised value to a boolean.

collapseDefault :: KnownVal (b :: t) => WithDefault b -> t
collapseDefault = \case
  w@Default -> knownVal w
  Value b -> b
