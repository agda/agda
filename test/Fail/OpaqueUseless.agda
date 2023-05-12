{-# OPTIONS --warning=error -WnoNotAffectedByOpaque #-}
module OpaqueUseless where

opaque
  data Foo : Set where
