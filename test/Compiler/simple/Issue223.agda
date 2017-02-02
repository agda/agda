{-# IMPORT Issue223 #-}

data A : Set
data B : Set

data A where
  BA : B → A

data B where
  AB : A → B
  BB : B

{-# COMPILED_DATA A Issue223.A Issue223.BA #-}
{-# COMPILED_DATA B Issue223.B Issue223.AB Issue223.BB #-}
