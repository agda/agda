
postulate
  A B : Set
  C : .{{_ : B}} → Set
  instance
    f : {{_ : A}} → B
  test : {{x : A}} → C
