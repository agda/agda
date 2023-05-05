{-# OPTIONS --cubical-compatible --safe --no-sized-types --no-guardedness --level-universe #-}

module Agda.Builtin.IO where

postulate IO : ∀ {a} → Set a → Set a
{-# POLARITY IO ++ ++ #-}
{-# BUILTIN IO IO #-}

{-# FOREIGN GHC type AgdaIO a b = IO b #-}
{-# COMPILE GHC IO = type AgdaIO #-}
