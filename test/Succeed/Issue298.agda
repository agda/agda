{-# OPTIONS --show-implicit #-}
{-# OPTIONS --sized-types #-}

module Issue298 where

open import Common.Size

data BTree : {i : Size} → Set where
  leaf : ∀ {i} → BTree {↑ i}
  node : ∀ {i} → BTree {i} → BTree {i} → BTree {↑ i}

recId : ∀ {i} → BTree {i} → BTree {i}
recId leaf = leaf
recId (node l r) = node (recId l) (recId r)

deepId : ∀ {i} → BTree {i} → BTree {i}
deepId leaf = leaf
deepId (node leaf leaf) = node leaf leaf
deepId (node leaf (node r1 r2)) = node leaf (node (deepId r1) (deepId r2))
deepId (node (node l1 l2) r) = node (node (deepId l1) (deepId l2)) (deepId r)
