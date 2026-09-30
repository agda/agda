
postulate
  A : Set

data B : Set where
  x : A → B

f : A → A
f = {!!} -- C-c C-c yields 'f x = ?', which fails to type check
