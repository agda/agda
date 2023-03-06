{-# OPTIONS --erased-cubical --level-universe #-}
module Common.Path where

open import Agda.Builtin.Cubical.Path public
open import Agda.Builtin.Cubical.HCompU
open import Agda.Primitive.Cubical renaming (primINeg to ~_; primIMax to _∨_; primIMin to _∧_;
                                             primHComp to hcomp; primTransp to transp; primComp to comp;
                                             itIsOne to 1=1)
                                   public
open import Agda.Builtin.Cubical.Sub renaming (Sub to _[_↦_]; primSubOut to outS) public

open Helpers public
