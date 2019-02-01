
module builtinInModule where

module Str where

  postulate S : Set
  {-# BUILTIN STRING S #-}
  primitive primStringAppend : S → S → S

