
data A : Set where
  a : A

data T : A → Set where
  t : T a

postulate
  f : ∀ x → T x → Set

stuff : Set
stuff = f {!!} t

-- There should not be a (Checked) status for this module!
