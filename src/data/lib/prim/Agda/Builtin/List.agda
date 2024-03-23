{-# OPTIONS --cubical-compatible --safe --no-sized-types --no-guardedness --level-universe --type-based-termination #-}

module Agda.Builtin.List where

infixr 5 _∷_
data List {a} (A : Set a) : Set a where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A

{-# BUILTIN LIST List #-}

{-# COMPILE JS  List = function(x,v) {
  if (x.length < 1) { return v["[]"](); } else { return v["_∷_"](x[0], x.slice(1)); }
} #-}
{-# COMPILE JS [] = Array() #-}
{-# COMPILE JS _∷_ = function (x) { return function(y) { return Array(x).concat(y); }; } #-}
