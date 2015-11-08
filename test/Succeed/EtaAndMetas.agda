-- {-# OPTIONS --show-implicit #-}
-- {-# OPTIONS -v tc:20 -v tc.pos.occ:20 -v tc.mod.apply:80 -v tc.signature:30 #-}
module EtaAndMetas where

record ⊤ : Set where

record Functor {_ : ⊤} : Set₁ where
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
