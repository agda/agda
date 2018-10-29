postulate
  R : Set → Set1
  r : {X : Set} {{ _ : R X }} → X → Set
  A : Set
  a : A

instance
  RI : R A
  -- RI = {!!} -- uncommenting lets instance resolution succeed

foo : r a
