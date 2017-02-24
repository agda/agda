{-# FOREIGN GHC import qualified Issue223 #-}

data A : Set
data B : Set

data A where
  BA : B → A

data B where
  AB : A → B
  BB : B

{-# COMPILE GHC A = data Issue223.A (Issue223.BA) #-}
{-# COMPILE GHC B = data Issue223.B (Issue223.AB | Issue223.BB) #-}
