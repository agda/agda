
record C (A : Set) : Set where
  field f : A → A

open C {{...}}

module M (A : Set) where
  data D : Set where
    d : A → D

  instance
    CD : C D
    CD = record { f = λ x → x }

data Bool : Set where
  false true : Bool

open M Bool

-- Bug: M.CD is not considered in instance search
x : D
x = f (M.d false)
