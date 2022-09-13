{-# OPTIONS --without-K --safe --no-sized-types --no-guardedness #-}

module Agda.Builtin.IO where

postulate IO : ∀ {a} → Set a → Set a
{-# POLARITY IO ++ ++ #-}
{-# BUILTIN IO IO #-}

{-# FOREIGN GHC type AgdaIO a = IO #-}
{-# COMPILE GHC IO = type(1) AgdaIO #-}
