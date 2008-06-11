module ForallForParameters
         (F : Set -> Set -> Set) X {Y} (Z : F X Y) where

module M A {B} (C : F A B) where

  data D : Set -> Set where
    d : A -> D A

  data P A : D A -> Set where

  codata Q {A} X : P A X -> Set where

module N I J K = M I {J} K
open module O I J K = N I J K
