-- Having all checkers disabled means that all recursive functions are non-terminating
{-# OPTIONS --no-type-based-termination --no-syntax-based-termination #-}
module TypeBasedTermination.AllCheckersDisabled where

f : {A : Set} → A
f = f
