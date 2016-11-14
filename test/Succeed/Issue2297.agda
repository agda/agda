
record R : Set₁ where
  field
    A : Set

module _ (r : R) where

  open R r

  data D : Set where
    c : A → D

  data P : D → Set where
    d : (x : A) → P (c x)

  postulate
    f : D → A

  g : (x : D) → P x → D
  g x (d y) with Set
  g x (d y) | _ = x
