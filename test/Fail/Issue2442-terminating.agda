{-# OPTIONS --safe #-}

module Issue2442-terminating where

{-# NON_TERMINATING #-}
f : Set
f = f
