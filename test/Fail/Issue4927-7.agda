data D : Set where
  c : D → D

pattern q (@♭ x) = c x
