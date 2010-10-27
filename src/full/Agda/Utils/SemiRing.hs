
module Agda.Utils.SemiRing where

class SemiRing a where
  oplus  :: a -> a -> a
  otimes :: a -> a -> a

instance SemiRing a => SemiRing (Maybe a) where
  oplus Nothing y = y
  oplus x Nothing = x
  oplus (Just x) (Just y) = Just (oplus x y)

  otimes Nothing _ = Nothing
  otimes _ Nothing = Nothing
  otimes (Just x) (Just y) = Just (otimes x y)
