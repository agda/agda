
postulate
  A B C : Set

module M where

  infixl 4 _+_
  infixl 6 _*_

  postulate
    _+_ _*_ : Set → Set → Set

  T : Set
  T = A + B * C

open M renaming (_*_ to infix 2 _*_)

test : T → A + B * C
test x = x  -- should use the updated fixity when printing the value of T !
