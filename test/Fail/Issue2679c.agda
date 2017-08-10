postulate
  A : Set

data B (a : A) : Set where
  conB : B a → B a

data C (a : A) : B a → Set where
  conC : (b : B a) → C a (conB b)

goo : (a1 a2 a3 : A) (c : C a1 _) → Set
goo a1 a2 a3 (conC b) = {!!}
