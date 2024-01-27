-- The usage of not-fully-applied type in constructor is considered recursive
{-# OPTIONS --type-based-termination --no-syntax-based-termination #-}
module TypeBasedTermination.PartiallyAppliedTypeInConstructor where


data U : Set where
  u : U

data L (A : U → Set) : Set where
  nil : L A
  cons : A u → L A


data T (ua : U) : Set where
  g : L T → T ua

foo : T u → U
foo (g nil) = u
foo (g (cons t)) = foo t
