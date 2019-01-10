module DuplicateBuiltinBinding where

postulate String : Set

{-# BUILTIN STRING String #-}
{-# BUILTIN STRING String #-}

