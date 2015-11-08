{- This example used to fail but after the point-free evaluation fix
   it seems to work #-}
module Issue259c where

postulate
  A : Set
  a : A
  b : ({x : A} → A) → A
  C : A → Set

d : {x : A} → A
d {x} = a

e : A
e = b (λ {x} → d {x})

F : C e → Set₁
F _ with Set
F _ | _ = Set
