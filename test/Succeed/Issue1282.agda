
data A (B : Set) : Set where
module C where
  record D : Set where
module E (F : Set) (G : A F) where
  open C public using (module D)
module H (I : Set) (J : A I) where
  open E I J using ()
