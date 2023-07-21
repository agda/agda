{-# OPTIONS -WnoNotAffectedByOpaque #-}
module OpaqueUselessNested where

opaque opaque opaque
  data Foo : Set where
