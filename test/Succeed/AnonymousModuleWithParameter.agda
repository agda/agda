module _ where

-- open import Common.Prelude

module Id (A : Set) where

  id : A → A
  id x = x

module _ (A : Set) where
  open Id A

  id2 = id
