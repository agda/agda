module ChangeFixity where

postulate
  A : Set
  B : Set
  result : B

module Product where
  infixr 4 _×_
  _×_ : A → B → B
  a × b = b

  infixr 3 _,_
  _,_ : A → A → B
  a , b = result

open Product using (_×_) renaming (_,_ to infixr 5 _∷_)

solution : A → B
solution a = a × a ∷ a
