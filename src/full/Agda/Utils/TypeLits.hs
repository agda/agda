{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}

-- | Type level literals, inspired by GHC.TypeLits.

module Agda.Utils.TypeLits
  ( KnownBool
  , boolVal
  , KnownVal
  , knownVal
  ) where

-- | Singleton for type level values.
-- | A known value is one we can obtain a singleton for.

class KnownVal (v :: t) where
  knownVal :: forall proxy. proxy v -> t

-- | Type-level booleans.

instance KnownVal 'True  where knownVal _ = True
instance KnownVal 'False where knownVal _ = False

type KnownBool (b :: Bool) = KnownVal b

boolVal :: forall proxy b. KnownBool b => proxy b -> Bool
boolVal = knownVal
