
module Lib.Prelude where

id : {A : Set} -> A -> A
id x = x

_∘_ : {A : Set}{B : A -> Set}{C : {x : A} -> B x -> Set}
      (f : {x : A}(y : B x) -> C y)(g : (x : A) -> B x)(x : A) ->
      C (g x)
(f ∘ g) x = f (g x)
