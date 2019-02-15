{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Three-valued datatype

module Agda.Utils.WithDefault where

import Data.Proxy
import Data.Typeable

data WithDefault (b :: Bool) = Off | Default | On
  deriving (Eq, Show)

turnDefaultOff :: WithDefault b -> WithDefault b
turnDefaultOff t | t == Default = Off
                 | otherwise    = t

data SBool (b :: Bool) where
  STrue  :: SBool 'True
  SFalse :: SBool 'False

eraseSBool :: SBool b -> Bool
eraseSBool b = case b of
  STrue  -> True
  SFalse -> False

class KnownBool (b :: Bool) where
  singBool :: Proxy b -> SBool b

instance KnownBool 'True where
  singBool _ = STrue

instance KnownBool 'False where
  singBool _ = SFalse

boolValue :: KnownBool b => Proxy b -> Bool
boolValue = eraseSBool . singBool

collapseDefault :: forall b. KnownBool b => WithDefault b -> Bool
collapseDefault w = case w of
  Default -> boolValue (Proxy :: Proxy b)
  Off     -> False
  On      -> True

