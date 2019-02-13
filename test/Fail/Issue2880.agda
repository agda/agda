{-# OPTIONS --safe #-}

module Issue2880 where

app : {A : Set} → (A → A) → (A → A)
app f x = f x

{-# COMPILE GHC app = \ A f x -> f (app A f x) #-}

mutual

  id : {A : Set} → A → A
  id x = x

  {-# COMPILE GHC id = id' #-}

  id' : {A : Set} → A → A
  id' x = x

  {-# COMPILE GHC id' = id #-}
