{-# IMPORT Issue223 #-}

data A : Set
{-# COMPILED_DECLARE_DATA A Issue223.A #-}
data B : Set
{-# COMPILED_DECLARE_DATA B Issue223.B #-}

data A where
  BA : B → A
{-# COMPILED_DATA A Issue223.A Issue223.BA #-}

data B where
  AB : A → B
  BB : B
{-# COMPILED_DATA B Issue223.B Issue223.AB Issue223.BB #-}

