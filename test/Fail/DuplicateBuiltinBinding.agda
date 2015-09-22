module DuplicateBuiltinBinding where

postulate Int : Set

{-# BUILTIN INTEGER Int #-}
{-# BUILTIN INTEGER Int #-}

