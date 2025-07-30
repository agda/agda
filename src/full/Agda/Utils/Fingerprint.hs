{-# LANGUAGE RoleAnnotations, MagicHash #-}
-- | Compact representations for type-indexed 'Fingerprint's.
module Agda.Utils.Fingerprint
  ( Fingerprint
  , sameFingerprint
  , typeFingerprint
  )
  where

import Data.Typeable (Typeable, (:~:)(Refl), Proxy, typeRep, typeRepFingerprint)

import qualified GHC.Fingerprint.Type as P

import Unsafe.Coerce

-- | A 'Fingerprint' parametrised over the type it represents but which
-- stores as a single Word64.
newtype Fingerprint a = Fingerprint { theFingerprint :: P.Fingerprint }
type role Fingerprint nominal

-- | Compare fingerprints, returning evidence that the types are
-- identical when they match.
sameFingerprint :: forall a b. Fingerprint a -> Fingerprint b -> Maybe (a :~: b)
sameFingerprint (Fingerprint a) (Fingerprint b)
  | a == b    = Just (unsafeCoerce Refl)
  | otherwise = Nothing

-- 2023-10-2 András: `typeRepFingerprint` usually inlines a 4-way case, which
-- yields significant code size increase as GHC often inlines the same code into
-- the branches. This wouldn't matter in "normal" code but the serialization
-- instances use very heavy inlining. The NOINLINE cuts down on the code size.
typeFingerprint :: forall a. Typeable a => Proxy a -> Fingerprint a
typeFingerprint rep = Fingerprint (typeRepFingerprint (typeRep rep))
{-# NOINLINE typeFingerprint #-}
