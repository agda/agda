{-# OPTIONS --no-termination-check #-}
module SafeFlagNoTermination where

data Empty : Set where

inhabitant : Empty
inhabitant = inhabitant