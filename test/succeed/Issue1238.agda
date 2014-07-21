
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

open M

-- Bug: M.CD is not considered in instance search
x : D Bool
x = f (d false)
