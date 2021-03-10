{-# OPTIONS --rewriting --confluence-check #-}
module Issue4333.N0 where

open import Issue4333.M
{-# REWRITE p₀ #-}

b₀' : B a₀'
b₀' = b
