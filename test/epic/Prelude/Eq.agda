{-# OPTIONS --universe-polymorphism #-}
module Prelude.Eq where

open import Prelude.Level

infix 4 _==_

data _==_ {l : Level}{A : Set l} (x : A) : A → Set l where
       refl : x == x
       

cong : {A : Set}{B : Set}{x y : A}(f : A -> B) -> x == y -> f x == f y
cong f refl = refl

{-# BUILTIN EQUALITY _==_  #-}
{-# BUILTIN REFL     refl #-}
