
module Zipper where

  import Derivative
  import Functor
  import Sets

  open Functor
  open Derivative
  open Semantics
  open Recursive
  open Sets

  Zipper : U -> Set
  Zipper F = List (⟦ ∂ F ⟧ (μ F))

  -- Plugging a zipper
  unzip : {F : U} -> Zipper F -> μ F -> μ F
  unzip	    []	     t = t
  unzip {F} (c :: γ) t = inn (plug-∂ F c (unzip γ t))

