{-# OPTIONS --sized-types #-}

module Rose where

postulate
  Size : Set
  _^   : Size -> Size
  ∞    : Size

{-# BUILTIN SIZE Size  #-}
{-# BUILTIN SIZESUC _^ #-}
{-# BUILTIN SIZEINF ∞  #-}

data List (A : Set) : {_ : Size} -> Set where
  []   : {size : Size} -> List A {size ^}
  _::_ : {size : Size} -> A -> List A {size} -> List A {size ^}

map : {A B : Set} -> (A -> B) -> 
      {size : Size} -> List A {size} -> List B {size}
map f [] = []
map f (x :: xs) = f x :: map f xs

data Rose (A : Set) : {_ : Size} -> Set where
  rose : {size : Size} -> A -> List (Rose A {size}) {∞} -> Rose A {size ^}

{-
mapRose : {A B : Set} -> (A -> B) -> 
          {size : Size} -> Rose A {size} -> Rose B {size}
mapRose {A} {B} f .{size ^} (rose {size} a l) =
   rose (f a) (map (\ r -> mapRose {A} {B} f {size} r) l)
-}

mapRose : {A B : Set} -> (A -> B) -> 
          {size : Size} -> Rose A {size} -> Rose B {size}
mapRose f (rose a l) = rose (f a) (map (mapRose f) l)

