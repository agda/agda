-- Andreas, 2026-11-19, issue #8608 reported by @clearnature
-- Primitive modules are not recognized as such
-- if they are symlinks in the Agda installation directory
-- rather than files.

{-# OPTIONS --safe #-}

module Issue8608 where

open import Agda.Builtin.Bool
