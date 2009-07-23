-- Builtin things aren't allowed inside parameterised modules. It's not clear
-- what that would mean.
module BuiltinInParameterisedModule where

module A (X : Set) where
  {-# BUILTIN INTEGER X #-}

