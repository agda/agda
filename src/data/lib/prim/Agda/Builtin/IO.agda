{-# OPTIONS --without-K --safe #-}

module Agda.Builtin.IO where

{-# BUILTIN IO IO #-}

{-# FOREIGN GHC type AgdaIO a b = IO b #-}
{-# COMPILE GHC IO = type AgdaIO #-}
