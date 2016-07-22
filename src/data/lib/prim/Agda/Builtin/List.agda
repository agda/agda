{-# OPTIONS --without-K #-}

module Agda.Builtin.List where

infixr 5 _∷_
data List {a} (A : Set a) : Set a where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A

{-# BUILTIN LIST List #-}
{-# BUILTIN NIL  []   #-}
{-# BUILTIN CONS _∷_  #-}

{-# HASKELL type AgdaList a b = [b] #-}

{-# COMPILED_DATA List MAlonzo.Code.Agda.Builtin.List.AgdaList [] (:) #-}
{-# COMPILED_DATA_UHC List __LIST__ __NIL__ __CONS__ #-}

{-# COMPILED_JS List function(x,v) {
  if (x.length < 1) { return v["[]"](); } else { return v["_∷_"](x.slice(0,1), x.slice(1)); }
} #-}
{-# COMPILED_JS [] Array() #-}
{-# COMPILED_JS _∷_ function (x) { return function(y) { return Array(x).concat(y); }; } #-}
