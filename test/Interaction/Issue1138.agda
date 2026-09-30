-- Andreas, 2014-05-21, reported and test case by Fabien Renaud

module Issue1138 where

open import Common.Equality

postulate
  Var    : Set
  Varset : Set
  _∖_    : Varset -> Var -> Varset
  _⊆_    : Varset -> Varset -> Set

data Expression : Set where
  abs : Var -> Expression -> Expression

FV : Expression -> Varset
FV (abs x M) = FV M ∖ x

data Env (A : Set) : Set where
  <>     : Env A
  _,_:=_ : Env A -> Var -> A -> Env A

postulate
  dom        : ∀ {A} -> Env A -> Varset
  extend-dom : ∀ {A : Set} {a : A} {x xs ρ}
               -> (xs ∖ x) ⊆ dom ρ
               -> xs ⊆ dom (ρ , x := a)

record Model (D : Set) : Set where
  field
    eval : (e : Expression) (ρ : Env D) -> FV e ⊆ dom ρ -> D
    d    : D
    law  : ∀ {M N ρ ν x y}
           -> eval M (ρ , x := d) (extend-dom {!!}) ≡
              eval N (ν , y := d) (extend-dom {!!})
           -> eval (abs x M) ρ {!!} ≡
              eval (abs y N) ν {!!}

-- Expected:  For holes numbered 0,1,2,3 above and four goals below:

-- ?0 : (FV M ∖ x) ⊆ dom ρ
-- ?1 : (FV N ∖ y) ⊆ dom ν
-- ?2 : FV (abs x M) ⊆ dom ρ
-- ?3 : FV (abs y N) ⊆ dom ν

-- There was a problem that two interaction points were created
-- per ? in record fields, thus, they were off in emacs.
-- (Introduced by fix for issue 1083).
