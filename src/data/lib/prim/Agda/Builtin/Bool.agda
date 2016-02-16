
module Agda.Builtin.Bool where

data Bool : Set where
  false true : Bool

{-# BUILTIN BOOL Bool   #-}
{-# BUILTIN TRUE true   #-}
{-# BUILTIN FALSE false #-}

{-# COMPILED_DATA_UHC Bool __BOOL__ __FALSE__ __TRUE__ #-}
