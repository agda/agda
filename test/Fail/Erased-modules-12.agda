-- Currently open public is not allowed in erased modules.

{-# OPTIONS --erasure --warning=error #-}

module _ where

import Agda.Builtin.Bool

module @0 Bool where

  _ : let open module M = Agda.Builtin.Bool public in Set₁
  _ = Set
