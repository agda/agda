
-- A.agda
{-# OPTIONS --rewriting #-}
module Issue7058.RewriteA where

postulate Rel : ∀{i}{A : Set i}(x y : A) → Set
{-# BUILTIN REWRITE Rel #-}

postulate a : Set₁

private
  b : Set₁
  b = Set
  postulate a~> : Rel a b
  {-# REWRITE a~> #-}
