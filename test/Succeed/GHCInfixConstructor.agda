
data Tree : Set where
  leaf : Tree
  _∣_ : Tree → Tree → Tree

{-# FOREIGN GHC data Tree = Leaf | Tree :| Tree #-}

{-# COMPILE GHC Tree = data Tree (Leaf | (:|)) #-}
