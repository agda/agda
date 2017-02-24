{-# OPTIONS --without-K #-}

module Agda.Builtin.Bool where

data Bool : Set where
  false true : Bool

{-# BUILTIN BOOL  Bool  #-}
{-# BUILTIN FALSE false #-}
{-# BUILTIN TRUE  true  #-}

{-# COMPILE UHC Bool = data __BOOL__ (__FALSE__ | __TRUE__) #-}

{-# COMPILE JS Bool  = function (x,v) { return ((x)? v["true"]() : v["false"]()); } #-}
{-# COMPILE JS false = false #-}
{-# COMPILE JS true  = true  #-}
