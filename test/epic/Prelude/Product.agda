module Prelude.Product where

infixr 4 _,_

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

open _×_ public
