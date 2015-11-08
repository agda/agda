
module RecordsAndModules where

module Setoids where

  record Equiv (a : Set) : Set where
    field
      x : a
      y : a

  record Setoid : Set1 where
    field
      carrier : Set
      equiv   : Equiv carrier

module RegExps (S : Setoids.Setoid) where

  data RegExp : Set where
    ε : RegExp

module SimpleMatcher (S : Setoids.Setoid) where

  open module R = RegExps S

  foo : RegExp -> RegExp
  foo ε = ε
