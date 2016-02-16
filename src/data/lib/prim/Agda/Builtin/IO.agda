
module Agda.Builtin.IO where

postulate IO : ∀ {a} → Set a → Set a
{-# BUILTIN IO IO #-}
