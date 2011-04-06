module AgdalightTelescopeSyntax where

postulate
  A : Set
  B : A -> Set
  g : (x y : A; z : B x) -> A
-- this is Agdalight syntax, should not parse