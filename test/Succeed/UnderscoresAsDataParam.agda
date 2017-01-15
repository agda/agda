-- We can let Agda infer the parameters of the constructor target

data List (A : Set) : Set where
  nil  : List _
  cons : A → List A → List _

-- 2017-01-12, Andreas: we can even omit the whole target
-- (for parameterized data types, but not inductive families)

data Bool : Set where
  true false : _

data Maybe (A : Set) : Set where
  nothing : _
  just : (x : A) → _
