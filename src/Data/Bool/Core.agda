------------------------------------------------------------------------
-- The Agda standard library
--
-- The type for booleans
------------------------------------------------------------------------
module Data.Bool.Core where

data Bool : Set where
  true  : Bool
  false : Bool

{-# BUILTIN BOOL  Bool  #-}
{-# BUILTIN TRUE  true  #-}
{-# BUILTIN FALSE false #-}

{-# COMPILED_DATA Bool Bool True False #-}

{-# COMPILED_JS Bool  function (x,v) { return ((x)? v["true"]() : v["false"]()); } #-}
{-# COMPILED_JS true  true  #-}
{-# COMPILED_JS false false #-}
