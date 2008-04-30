------------------------------------------------------------------------
-- Sums (disjoint unions)
------------------------------------------------------------------------

module Data.Sum where

open import Data.Function
open import Relation.Binary.PropositionalEquality

infixr 1 _-⊎-_

------------------------------------------------------------------------
-- Definition

open import Data.Sum.Core public

------------------------------------------------------------------------
-- Functions

[_,_] :  {a b c : Set}
      -> (a -> c) -> (b -> c) -> (a ⊎ b -> c)
[ f , g ] (inj₁ x) = f x
[ f , g ] (inj₂ y) = g y

map-⊎ :  {a b c d : Set}
      -> (a -> c) -> (b -> d) -> (a ⊎ b -> c ⊎ d)
map-⊎ f g = [ inj₁ ∘ f , inj₂ ∘ g ]

_-⊎-_ :  {a b : Set}
      -> (a -> b -> Set) -> (a -> b -> Set) -> (a -> b -> Set)
f -⊎- g = f -[ _⊎_ ]₁- g

------------------------------------------------------------------------
-- Properties

inj₁≢inj₂ : forall {a b} {x : a} {y : b} -> inj₁ x ≢ inj₂ y
inj₁≢inj₂ ()
