{-# OPTIONS --no-main #-}

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

{-# COMPILE GHC List = data Non (Sense) #-} -- should result in warning when compiling
{-# BUILTIN LIST List #-}
{-# BUILTIN NIL  []   #-}
{-# BUILTIN CONS _∷_  #-}
