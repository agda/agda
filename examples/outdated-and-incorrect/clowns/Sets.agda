
module Sets where

  import Equality
  open Equality public

  infixr 10 _$_
  infixr 40 _[+]_ _<+>_ _>+<_
  infixr 60 _[×]_ _<×>_ _>×<_
  infixr 90 _∘_

  id : {A : Set} -> A -> A
  id x = x

  _∘_ : {A B C : Set} -> (B -> C) -> (A -> B) -> A -> C
  f ∘ g = \x -> f (g x)

  _$_ : {A B : Set} -> (A -> B) -> A -> B
  f $ x = f x

  data _[+]_ (A B : Set) : Set where
    inl : A -> A [+] B
    inr : B -> A [+] B

  _<+>_ : {A₁ A₂ B₁ B₂ : Set} -> (A₁ -> A₂) -> (B₁ -> B₂) -> A₁ [+] B₁ -> A₂ [+] B₂
  (f <+> g) (inl x) = inl (f x)
  (f <+> g) (inr y) = inr (g y)

  _>+<_ : {A B C : Set} -> (A -> C) -> (B -> C) -> A [+] B -> C
  (f >+< g) (inl x) = f x
  (f >+< g) (inr y) = g y

  data _[×]_ (A B : Set) : Set where
    <_,_> : A -> B -> A [×] B

  -- sections
  <∙,_> : {A B : Set} -> B -> A -> A [×] B
  <∙, x > = \y -> < y , x >

  <_,∙> : {A B : Set} -> A -> B -> A [×] B
  < x ,∙> = \y -> < x , y >

  _<×>_ : {A₁ A₂ B₁ B₂ : Set} -> (A₁ -> A₂) -> (B₁ -> B₂) -> A₁ [×] B₁ -> A₂ [×] B₂
  (f <×> g) < x , y > = < f x , g y >

  _>×<_ : {A B C : Set} -> (A -> B) -> (A -> C) -> A -> B [×] C
  (f >×< g) x = < f x , g x >

  fst : {A B : Set} -> A [×] B -> A
  fst < a , b > = a

  snd : {A B : Set} -> A [×] B -> B
  snd < a , b > = b

  η-[×] : {A B : Set}(p : A [×] B) -> p == < fst p , snd p >
  η-[×] < a , b > = refl

  data [1] : Set where
    <> : [1]

  data [0] : Set where

  data List (A : Set) : Set where
    []   : List A
    _::_ : A -> List A -> List A

