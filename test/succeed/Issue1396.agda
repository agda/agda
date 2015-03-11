
module _ where

postulate
  A : Set
  _,_ : A → A → A

module M where
  module Mx (x : A) where
    module M where
      module My (y : A) where
        f : A
        f = x , y

postulate
  a b c : A

module M′  = M
module Ma  = M′.Mx.M a
module Mab = Ma.My b

g : A
g =  Mab.f

-- Original bug report --

record I (A : Set) : Set where
  field
    i : A → A
  record R (A : Set) : Set where
    field
      f : A → A
  open R public

module C (A : Set) where
  I₀ : I A
  I₀ = record { i = λ x → x }

  open I I₀

  r : (B : Set) → R B
  r B = record { f = λ x → x }

  g1 : (B : Set) → B → B
  g1 B = f′
    where
      open R (r B) renaming (f to f′)
