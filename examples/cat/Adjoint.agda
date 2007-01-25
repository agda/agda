
module Adjoint where

import Category
import Functor

open Category
open Functor using (Functor)

module Adj where

  open Functor.Projections using (Map; map)

  data _⊢_ {ℂ ⅅ : Cat}(F : Functor ℂ ⅅ)(G : Functor ⅅ ℂ) : Set1 where
    adjunction :
      (_*   : {X : Obj ℂ}{Y : Obj ⅅ} -> Map F X ─→ Y -> X ─→ Map G Y)
      (_#   : {X : Obj ℂ}{Y : Obj ⅅ} -> X ─→ Map G Y -> Map F X ─→ Y)
      (inv₁ : {X : Obj ℂ}{Y : Obj ⅅ}(g : X ─→ Map G Y) -> g # * == g)
      (inv₂ : {X : Obj ℂ}{Y : Obj ⅅ}(f : Map F X ─→ Y) -> f * # == f)
      (nat₁ : {X₁ X₂ : Obj ℂ}{Y₁ Y₂ : Obj ⅅ}
	      (f : Y₁ ─→ Y₂)(g : X₂ ─→ X₁)(h : Map F X₁ ─→ Y₁) ->
	      (f ∘ h ∘ map F g) * == map G f ∘ (h *) ∘ g
      )
      (nat₂ : {X₁ X₂ : Obj ℂ}{Y₁ Y₂ : Obj ⅅ}
	      (f : Y₁ ─→ Y₂)(g : X₂ ─→ X₁)(h : X₁ ─→ Map G Y₁) ->
	      (map G f ∘ h ∘ g) # == f ∘ (h #) ∘ map F g
      )
      -> F ⊢ G

open Adj public

