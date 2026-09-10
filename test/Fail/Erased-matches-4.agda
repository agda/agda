-- The option --erased-matches=none does not enable erasure.

{-# OPTIONS --erased-matches=none #-}

id : {@0 A : Set} → A → A
id x = x
