module Issue606 where

infixr 1 _,_

record _×_ (A B : Set) : Set where
  constructor _,_
  field fst : A
        snd : B

postulate A B C : Set

test : A × (B × C)
test = {!!} , {!!}
-- refining the second hole should give "? , ?"  (no enclosing parens!)
