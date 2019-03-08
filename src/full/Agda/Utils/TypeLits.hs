{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs          #-}


-- | Type level literals, inspired by GHC.TypeLits.

module Agda.Utils.TypeLits where

-- | Singleton for type level booleans.

data SBool (b :: Bool) where
  STrue  :: SBool 'True
  SFalse :: SBool 'False

eraseSBool :: SBool b -> Bool
eraseSBool b = case b of
  STrue  -> True
  SFalse -> False

-- | A known boolean is one we can obtain a singleton for.
--   Concrete values are trivially known.

class KnownBool (b :: Bool) where
  boolSing :: SBool b

instance KnownBool 'True where
  boolSing = STrue

instance KnownBool 'False where
  boolSing = SFalse

boolVal :: forall proxy b. KnownBool b => proxy b -> Bool
boolVal _ = eraseSBool (boolSing :: SBool b)
