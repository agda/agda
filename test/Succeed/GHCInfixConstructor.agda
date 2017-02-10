
data Tree : Set where
  leaf : Tree
  _∣_ : Tree → Tree → Tree

{-# HASKELL data Tree = Leaf | Tree :| Tree #-}

{-# COMPILED_DATA Tree Tree Leaf (:|) #-}
