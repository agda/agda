{-# OPTIONS --safe #-} -- implies --no-sized-types

module Issue3517.M where

open import Issue3517.S

f : (i : Size) (j : Size< i) → Size< j → Size< i
f i j k = k
