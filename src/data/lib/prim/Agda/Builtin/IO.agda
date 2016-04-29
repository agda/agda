{-# OPTIONS --without-K #-}

module Agda.Builtin.IO where

postulate IO : ∀ {a} → Set a → Set a
{-# BUILTIN IO IO #-}

{-# HASKELL type AgdaIO a b = IO b #-}
{-# COMPILED_TYPE IO MAlonzo.Code.Agda.Builtin.IO.AgdaIO #-}
