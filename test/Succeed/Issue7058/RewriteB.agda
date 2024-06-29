
-- B.agda
{-# OPTIONS --rewriting #-}

module Issue7058.RewriteB where
open import Issue7058.RewriteA

postulate c : Set

_ : a
_ = c
