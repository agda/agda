{-# OPTIONS --sized-types #-}
module GiveSize where

postulate Size : Set
{-# BUILTIN SIZE Size #-}

id : Size → Size
id i = {!i!}
