postulate
  A B : Set
  f : A → B

data D : B → Set where
  c : {n : A} → D (f n)

test : (x : B) → D x → Set
test n c = {!!}

test2 : Set
test2 =
  let X = A in
  let X = B in
  {!!}
