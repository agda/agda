module ReducingConstructorsInWith where

data ⊤ : Set where
  tt : ⊤

module RegExps where

  data RegExp : Set where
    _│_ : RegExp -> RegExp -> RegExp

open module R = RegExps

bypassable : (re : RegExp) -> ⊤
bypassable (re₁ │ re₂) with bypassable re₁
bypassable (re₁ │ re₂) | m  = m

