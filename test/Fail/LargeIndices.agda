
-- Only forced indices can be large.

data Img {a b} {A : Set a} {B : Set b} (f : A → B) : B → Set where
  inv : ∀ x → Img f (f x)
