-- Andreas, 2012-02-14. No short-circuit conversion test for sizes!
{-# OPTIONS --sized-types --show-implicit #-} 
-- {-# OPTIONS -v tc.size.solve:20 -v tc.conv.size:20 -v tc.term.con:50 -v tc.term.args:50 #-}

module Issue298b where

open import Common.Size

data BTree : {size : Size} → Set where
  leaf : {i : Size} → BTree {↑ i}
  node : {i : Size} → BTree {i} → BTree {i} → BTree {↑ i}

works : ∀ {i} → BTree {i} → BTree
works (node (node t1 t2) t3) = node (works t1) (node t2 t3)
works t = t
