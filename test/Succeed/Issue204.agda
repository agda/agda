{-# OPTIONS --universe-polymorphism #-}
module Issue204 where

open import Issue204.Dependency

postulate
  ℓ : Level
  r : R ℓ
  d : D ℓ

open R r

open M d
