-- type-based termination works here because encoding was implicitly enabled in an imported module
{-# OPTIONS --type-based-termination --no-syntax-based-termination #-}
module TypeBasedTermination.EncodingExplicitlyDisabled where

open import TypeBasedTermination.Module.WithExplicitNoEncodingPragma

mapRose : ∀ {A B} → (A → B) → Rose A → Rose B
mapRose f (rose a rs) = rose (f a) (map (mapRose f) rs)
