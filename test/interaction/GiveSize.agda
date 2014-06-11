-- {-# OPTIONS -v tc.meta:30 #-}
{-# OPTIONS --sized-types #-}
module GiveSize where

postulate Size : Set
postulate ∞ : Size
{-# BUILTIN SIZE Size #-}
-- {-# BUILTIN SIZEINF ∞ #-}

id : Size → Size
id i = {!i!}
