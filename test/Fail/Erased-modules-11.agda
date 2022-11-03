-- Currently open public is not allowed in erased modules.

{-# OPTIONS --warning=error #-}

module _ where

import Agda.Builtin.Bool

module @0 Bool where

  _ : let open Agda.Builtin.Bool public in Set₁
  _ = Set
