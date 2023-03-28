{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds      #-}

-- | Potentially uninitialised Booleans.
--
-- The motivation for this small library is to distinguish
-- between a boolean option with a default value and an option which has been
-- set to what happens to be the default value.  In one case the default can be
-- overriden (e.g. @--cubical@ implies @--without-K@) while in the other case the
-- user has made a mistake which they need to fix.

module Agda.Utils.WithDefault where

import Control.DeepSeq

import Agda.Utils.Null
import Agda.Utils.TypeLits

-- | We don't want to have to remember for each flag whether its default value
-- is @True@ or @False@. So we bake it into the representation: the flag's type
-- will mention its default value as a phantom parameter.
--
data WithDefault (b :: Bool) = Default | Value !Bool
  deriving (Eq, Show)

instance NFData (WithDefault b) where
  rnf Default   = ()
  rnf (Value _) = ()

-- | The null value of 'WithDefault b' is 'Default'.
--
instance Null (WithDefault b) where
  empty = Default
  null = \case
    Default -> True
    Value _ -> False

-- | The main mode of operation of these flags, apart from setting them explicitly,
-- is to toggle them one way or the other if they hadn't been set already.
--
setDefault :: Bool -> WithDefault b -> WithDefault b
setDefault b = \case
  Default -> Value b
  t -> t

-- | Provided that the default value is a known boolean (in practice we only use
-- @True@ or @False@), we can collapse a potentially uninitialised value to a boolean.
--
collapseDefault :: KnownBool b => WithDefault b -> Bool
collapseDefault = \case
  w@Default -> boolVal w
  Value b -> b

-- | Update, overwriting 'Default'.
--
mapCollapseDefault :: KnownBool b => (Bool -> Bool) -> WithDefault b -> WithDefault b
mapCollapseDefault f = Value . f . collapseDefault

-- | Update, but keep 'Default' when new value is default value.
--
mapKeepDefault :: KnownBool b => (Bool -> Bool) -> WithDefault b -> WithDefault b
mapKeepDefault f = \case
  Value b   -> Value (f b)
  w@Default -> if b == b' then Default else Value b'
    where
    b  = boolVal w
    b' = f b

-- | Set, but keep 'Default' when new value is default value.
--
setKeepDefault :: KnownBool b => Bool -> WithDefault b -> WithDefault b
setKeepDefault = mapKeepDefault . const
