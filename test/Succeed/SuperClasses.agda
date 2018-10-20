module _ where

open import Common.Prelude
open import Common.Equality

record Functor (F : Set → Set) : Set₁ where
  field
    fmap : ∀ {A B} → (A → B) → F A → F B

open Functor {{...}} public

record Applicative (F : Set → Set) : Set₁ where
  field
    pure    : ∀ {A} → A → F A
    _<*>_   : ∀ {A B} → F (A → B) → F A → F B
    {{Fun}} : Functor F

  defaultApplicativeFunctor : Functor F
  fmap {{defaultApplicativeFunctor}} f x = pure f <*> x

open Applicative {{...}} public hiding (Fun)

-- Concrete instances --

data Vec (A : Set) : Nat → Set where
  [] : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

vmap : ∀ {A B n} → (A → B) → Vec A n → Vec B n
vmap f [] = []
vmap f (x ∷ xs) = f x ∷ vmap f xs

it : ∀ {a} {A : Set a} {{_ : A}} → A
it {{x}} = x

pureV : ∀ {n A} → A → Vec A n
pureV {zero} _ = []
pureV {suc n} x = x ∷ pureV x

instance
  FunctorVec : ∀ {n} → Functor (λ A → Vec A n)
  fmap {{FunctorVec}} = vmap

  ApplicativeVec : ∀ {n} → Applicative (λ A → Vec A n)
  pure  {{ApplicativeVec}} x = pureV x
  _<*>_ {{ApplicativeVec}} []       []       = []
  _<*>_ {{ApplicativeVec}} (f ∷ fs) (x ∷ xs) = f x ∷ (fs <*> xs)
  Applicative.Fun ApplicativeVec = FunctorVec

-- In this case there are two candidates for Functor Vec:
--   FunctorVec and Applicative.Fun ApplicativeVec
-- but since they are equal everything works out.
testVec : ∀ {n} → Vec Nat n → Vec Nat n → Vec Nat n
testVec xs ys = fmap _+_ xs <*> ys

what : ∀ {n} → FunctorVec {n} ≡ it
what = refl

zipWith : {A B C : Set} {F : Set → Set} {{_ : Applicative F}} →
          (A → B → C) → F A → F B → F C
zipWith f x y = fmap f x <*> y
