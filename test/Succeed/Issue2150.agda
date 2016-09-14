
open import Agda.Primitive

postulate
  X : Set
  Id : Set → Set

module Generic1HIT (S : Set) where
  module RecType k (C : Set k) (Necc : Set) where
    postulate P : Set

module Flattening k (F : Set → Set) (C : Set k) (Necc : Set) where
  -- order f before C matters!
  module W = Generic1HIT (F X)  -- use of F matters, application of F matters
  module M = W.RecType k C X    -- k matters

module S¹RecType i (A : Set i) where
  module FlatteningS¹ = Flattening i Id A X    -- i matters here

module HopfJunior = S¹RecType _ Set  -- meta variable matters
