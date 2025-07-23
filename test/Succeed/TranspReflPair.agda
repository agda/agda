{-# OPTIONS --cubical -vtc.conv.term.cubical:30 #-}
module TranspReflPair where

open import Agda.Primitive.Cubical renaming (primIMax to _∨_ ; primINeg to ~_; primHComp to hcomp; primComp to comp; primTransp to transp)
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Sigma
open import Agda.Builtin.Nat

-- Transp on Σ behaves as though "defined by copattern matching" but the
-- conversion checker really wants to avoid eta-expanding cubical
-- primitives to not cause performance meltdowns when one or both sides
-- are blocked on a meta (rather than being good neutrals).
--
-- But in this case the transport is a pair that contains the same
-- components as the other pair and we can't skip it!

test1 : ∀ x → transp (λ i → Σ Nat λ _ → Nat) i0 x ≡ x
test1 x i = x
