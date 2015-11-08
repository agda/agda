module Issue180 where

module Example₁ where

  data C : Set where
    c : C → C

  data Indexed : (C → C) → Set where
    i : Indexed c

  foo : Indexed c → Set
  foo i = C

module Example₂ where

  data List (A : Set) : Set where
    nil  : List A
    cons : A → List A → List A

  postulate
    A : Set
    x : A

  T : Set
  T = List A → List A

  data P : List T → Set where
    p : (f : T) → P (cons f nil)

  data S : (xs : List T) → P xs → Set where
    s : (f : T) → S (cons f nil) (p f)

  foo : S (cons (cons x) nil) (p (cons x)) → A
  foo (s ._) = x
