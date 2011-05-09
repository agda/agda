-- Andreas, 2011-05-10
module MetaAppUnderLambda where

data _≡_ {A : Set} (a : A) : A -> Set where
  refl : a ≡ a

data D (A : Set) : Set where
  cons : A -> (A -> A) -> D A

f : {A : Set} -> D A -> A
f (cons a h) = a

test : (A : Set) ->
       let X : A
           X = _
           Y : A -> A
           Y = λ v -> _ v
       in  f (cons X Y) ≡ X
test A = refl
-- should return "Unsolved Metas"
-- executes the defauls A.App case in the type checker (which is not covered by appView)