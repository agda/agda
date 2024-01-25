-- Tests type alias in data definition
{-# OPTIONS --type-based-termination --no-syntax-based-termination #-}
module TypeBasedTermination.Aliases where

box : (A : Set) → Set
box A = A

data Wrp : Set where
  zw : Wrp
  zs : box Wrp → Wrp

foo : Wrp → Wrp
foo zw = zw
foo (zs w) = foo w
