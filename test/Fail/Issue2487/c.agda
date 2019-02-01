{-# OPTIONS --cubical --no-sized-types --no-guardedness #-}
module Issue2487.c where

postulate admit : {A : Set} -> A
