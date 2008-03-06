module Basics where

id : {A : Set} -> A -> A
id a = a

_o_ : {A : Set}{B : A -> Set}{C : (a : A)(b : B a) -> Set} ->
      ({a : A}(b : B a) -> C a b) -> (g : (a : A) -> B a) ->
      (a : A) -> C a (g a)
_o_ f g a = f (g a)
