module Agda.Utils.SemiRing where

-- | Semirings (<https://en.wikipedia.org/wiki/Semiring>).

class SemiRing a where
  ozero  :: a
  oone   :: a
  oplus  :: a -> a -> a
  otimes :: a -> a -> a

instance SemiRing a => SemiRing (Maybe a) where
  ozero = Nothing
  oone  = Just oone

  oplus Nothing y = y
  oplus x Nothing = x
  oplus (Just x) (Just y) = Just (oplus x y)

  otimes Nothing _ = Nothing
  otimes _ Nothing = Nothing
  otimes (Just x) (Just y) = Just (otimes x y)
