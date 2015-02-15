-- {-# OPTIONS -v tc.meta:30 #-}

module GiveSize where

{-# BUILTIN SIZE Size #-}

id : Size → Size
id i = {!i!}
