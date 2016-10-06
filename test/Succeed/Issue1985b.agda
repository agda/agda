
module _ where

postulate
  A B C D E F : Set
  a : A
  b : B
  c : C
  d : D
  e : E
  f : F
  T : {A : Set} → A → Set

module M1 (a : A) where
  module M2 (b : B) where
    postulate g : T a → T b
    module M3 (c : C) where
      postulate h : T a → T b → T c
  module M4 (d : D) where
    module M5 (e : E) (f : F) where
      open M2 public
      open M2.M3 public
      open M3 public renaming (h to h')

module M  = M1.M4 a d
module M' = M.M5 e f

M'g : (x : B) → T a → T x
M'g = M'.g

M'M3h M'h M'h' : (x : B) (y : C) → T a → T x → T y
M'M3h = M'.M3.h
M'h = M'.h
M'h' = M'.h'
