{-# OPTIONS --without-K #-}

module Agda.Builtin.Bool where

data Bool : Set where
  false true : Bool

{-# BUILTIN BOOL  Bool  #-}
{-# BUILTIN FALSE false #-}
{-# BUILTIN TRUE  true  #-}

{-# COMPILED_DATA_UHC Bool __BOOL__ __FALSE__ __TRUE__ #-}

{-# COMPILED_JS Bool  function (x,v) { return ((x)? v["true"]() : v["false"]()); } #-}
{-# COMPILED_JS false false #-}
{-# COMPILED_JS true  true  #-}
