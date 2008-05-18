
module Functor where

import Logic.Identity as Id
import Category
import Logic.ChainReasoning

open Category
open Poly-Cat

private
 module Fun where

  data Functor (ℂ ⅅ : Cat) : Set1 where
    functor : (F     : Obj ℂ -> Obj ⅅ)
	      (map   : {A B : Obj ℂ} -> A ─→ B -> F A ─→ F B)
	      (mapId : {A : Obj ℂ} -> map (id {A = A}) == id)
	      (mapCompose : {A B C : Obj ℂ}{f : B ─→ C}{g : A ─→ B} ->
			    map (f ∘ g) == map f ∘ map g
	      ) -> Functor ℂ ⅅ

open Fun public

module Projections where

  Map : {ℂ ⅅ : Cat} -> Functor ℂ ⅅ -> Obj ℂ -> Obj ⅅ
  Map (functor F _ _ _) = F

  map : {ℂ ⅅ : Cat}(F : Functor ℂ ⅅ)
	{A B : Obj ℂ} -> A ─→ B -> Map F A ─→ Map F B
  map (functor _ m _ _) = m

  mapId : {ℂ ⅅ : Cat}(F : Functor ℂ ⅅ)
	  {A : Obj ℂ} -> map F id == id {A = Map F A}
  mapId (functor _ _ i _) = i

  mapCompose : {ℂ ⅅ : Cat}(F : Functor ℂ ⅅ)
	       {A B C : Obj ℂ}{f : B ─→ C}{g : A ─→ B} ->
	       map F (f ∘ g) == map F f ∘ map F g
  mapCompose (functor _ _ _ c) = c

module Functor {ℂ ⅅ : Cat}(F : Functor ℂ ⅅ) where

  module P = Projections

  Map : Obj ℂ -> Obj ⅅ
  Map = P.Map F

  map : {A B : Obj ℂ} -> A ─→ B -> Map A ─→ Map B
  map = P.map F

  mapId : {A : Obj ℂ} -> map id == id {A = Map A}
  mapId = P.mapId F

  mapCompose : {A B C : Obj ℂ}{f : B ─→ C}{g : A ─→ B} ->
	       map (f ∘ g) == map f ∘ map g
  mapCompose = P.mapCompose F

module Functors where

  Id : {ℂ : Cat} -> Functor ℂ ℂ
  Id = functor (\A -> A) (\f -> f) (\{A} -> refl) (\{A}{B}{C}{f}{g} -> refl)

  _○_ : {ℂ ℚ ℝ : Cat} -> Functor ℚ ℝ -> Functor ℂ ℚ -> Functor ℂ ℝ
  _○_ {ℂ}{ℚ}{ℝ} F G = functor FG m mid mcomp
    where

      module F = Functor F
      module G = Functor G

      FG : Obj ℂ -> Obj ℝ
      FG A = F.Map (G.Map A)

      m : {A B : Obj ℂ} -> A ─→ B -> FG A ─→ FG B
      m f = F.map (G.map f)

      mid : {A : Obj ℂ} -> m (id {A = A}) == id
      mid = chain> F.map (G.map id)
	       === F.map id   by ? -- cong F.map G.mapId
	       === id	      by F.mapId
	where
	  open module Chain = Logic.ChainReasoning.Mono.Homogenous _==_
			      (\f -> refl)
			      (\f g h -> trans)

      mcomp : {A B C : Obj ℂ}{f : B ─→ C}{g : A ─→ B} ->
	      m (f ∘ g) == m f ∘ m g
      mcomp {f = f}{g = g} =
	chain> F.map (G.map (f ∘ g))
	   === F.map (G.map f ∘ G.map g)
	       by ? -- cong F.map G.mapCompose
	   === F.map (G.map f) ∘ F.map (G.map g)
	       by F.mapCompose
	where
	  open module Chain = Logic.ChainReasoning.Mono.Homogenous _==_
			      (\f -> refl)
			      (\f g h -> trans)


