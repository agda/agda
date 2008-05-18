
module Logic.Leibniz where

-- Leibniz equality
_≡_ : {A : Set} -> A -> A -> Set1
x ≡ y = (P : _ -> Set) -> P x -> P y

≡-refl : {A : Set}(x : A) -> x ≡ x
≡-refl x P px = px

≡-sym : {A : Set}(x y : A) -> x ≡ y -> y ≡ x
≡-sym x y xy P py = xy (\z -> P z -> P x) (\px -> px) py

≡-trans : {A : Set}(x y z : A) -> x ≡ y -> y ≡ z -> x ≡ z
≡-trans x y z xy yz P px = yz P (xy P px)

≡-subst : {A : Set}(P : A -> Set)(x y : A) -> x ≡ y -> P x -> P y
≡-subst P _ _ xy = xy P

