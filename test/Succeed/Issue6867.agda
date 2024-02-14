{-# OPTIONS --erasure #-}

postulate A : Set

data This : A → Set where
  this : (x : A) → This x

id-this : (@0 x : A) → This x → This x
id-this _ (this x) = this x
