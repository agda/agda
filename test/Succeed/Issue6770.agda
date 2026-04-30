postulate A : Set

module M (x : A) where
  postulate a : A

variable x : A

module _ (open M x) where
  _ : A
  _ = a
