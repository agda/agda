{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE KindSignatures #-}

-- | Potentially uninitialised Booleans

-- The initial motivation for this small library is to be able to distinguish
-- between a boolean option with a default value and an option which has been
-- set to what happens to be the default value. In one case the default can be
-- overriden (e.g. --cubical implies --without-K) while in the other case the
-- user has made a mistake which they need to fix.

module Agda.Utils.WithDefault where

import Agda.Utils.TypeLits

-- We don't want to have to remember for each flag whether its default value
-- is True or False. So we bake it into the representation: the flag's type
-- will mention its default value as a phantom parameter.

data WithDefault (b :: Bool) = Default | Value Bool
  deriving (Eq, Show)

-- The main mode of operation of these flags, apart from setting them explicitly,
-- is to toggle them one way or the other if they hadn't been already.

setDefault :: Bool -> WithDefault b -> WithDefault b
setDefault b t = case t of
  Default -> Value b
  _ -> t

-- Provided that the default value is a known boolean (in practice we only use
-- True or False), we can collapse a potentially uninitialised value to a boolean.

collapseDefault :: KnownBool b => WithDefault b -> Bool
collapseDefault w = case w of
  Default -> boolVal w
  Value b -> b
