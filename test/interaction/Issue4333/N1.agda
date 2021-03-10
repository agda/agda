{-# OPTIONS --rewriting --confluence-check #-}
module Issue4333.N1 where

open import Issue4333.M
{-# REWRITE p₁ #-}

b₁' : B a₁'
b₁' = b
