module Agda.Utils.SemiRing where

-- | Semirings (<https://en.wikipedia.org/wiki/Semiring>).

class SemiRing a where
  ozero  :: a
  oone   :: a
  oplus  :: a -> a -> a
  otimes :: a -> a -> a

instance SemiRing () where
  ozero      = ()
  oone       = ()
  oplus  _ _ = ()
  otimes _ _ = ()

instance SemiRing a => SemiRing (Maybe a) where
  ozero = Nothing
  oone  = Just oone

  oplus Nothing y = y
  oplus x Nothing = x
  oplus (Just x) (Just y) = Just (oplus x y)

  otimes Nothing _ = Nothing
  otimes _ Nothing = Nothing
  otimes (Just x) (Just y) = Just (otimes x y)

-- | Star semirings
-- (<https://en.wikipedia.org/wiki/Semiring#Star_semirings>).

class SemiRing a => StarSemiRing a where
  ostar :: a -> a

instance StarSemiRing () where
  ostar _ = ()

instance StarSemiRing a => StarSemiRing (Maybe a) where
  ostar Nothing  = oone
  ostar (Just x) = Just (ostar x)
