module Issue978 where

module A where

  infixr 4 _,_

  record _×_ (A B : Set) : Set where
    constructor _,_
    field
      fst : A
      snd : B

module B where

  infixl 2 _,_

  data Ty : Set where

  data Cxt : Set where
    ε   : Cxt
    _,_ : (Γ : Cxt) (a : Ty) → Cxt

open A
open B

test : (Γ : Cxt) → Set₁
test ε = Set
test (ε , a) = ?
test (Γ , a , a₁) = ?
