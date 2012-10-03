
module EtaAndMetas where

record Functor : Set₁ where
  field
    F : Set → Set

eta : Functor → Functor
eta S = record { F = F }
  where open Functor S

postulate
  Π   : (To : Functor) → Set
  mkΠ : (B : Functor) → Π (eta B)
  To  : Functor

π : Π (eta To)
π = mkΠ _
