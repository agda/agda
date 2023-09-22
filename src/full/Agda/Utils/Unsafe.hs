{-# OPTIONS_GHC -Wunused-imports #-}

{-# LANGUAGE MagicHash #-}
module Agda.Utils.Unsafe (unsafeComparePointers) where

import GHC.Exts (reallyUnsafePtrEquality#, isTrue#)

-- | Checks if two arguments are equal as pointers in memory.
-- Please note, that this function is a hack, and it can worsen the behavior of compiler.
-- See https://gitlab.haskell.org/ghc/ghc/-/blob/d151546e59a50158f25c3df6728b00d3c27bb4b9/compiler/GHC/Builtin/primops.txt.pp#L3455
unsafeComparePointers :: a -> a -> Bool
unsafeComparePointers x y = x `seq` y `seq` isTrue# (reallyUnsafePtrEquality# x y)
