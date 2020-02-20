-- The bug appeared since I forgot to keep the constraint when trying to unify
-- a blocked term (I just didn't instantiate).
module LostConstraint where

  infixr 10 _=>_

  data Setoid : Set1 where
    setoid : Set -> Setoid

  El : Setoid -> Set
  El (setoid A) = A

  eq : (A : Setoid) -> El A -> El A -> Set
  eq (setoid A) = e
    where
      postulate e : (x, y : A) -> Set

  data _=>_ (A B : Setoid) : Set where
    lam : (f : El A -> El B)
       -> ((x : El A) -> eq A x x
                      -> eq B (f x) (f x)
          )
       -> A => B


  app : {A B : Setoid} -> (A => B) -> El A -> El B
  app (lam f _) = f

  postulate EqFun : {A B : Setoid}(f, g : A => B) -> Set

  lam2 : {A B C : Setoid} ->
         (f : El A -> El B -> El C) ->
         (x : El A) -> B => C
  lam2 {A}{B}{C} f x = lam (f x) (lem _)
    where
      postulate
        lem : (x : El A)(y : El B) -> eq B y y -> eq C (f x y) (f x y)
