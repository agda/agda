-- {-# OPTIONS -v tc.meta:30 #-}
{-# OPTIONS --show-implicit --show-irrelevant #-}
module Issue629 where

infixr 4 _,_
infixr 2 _×_

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

const : {A : Set₁} {B : Set} → A → (B → A)
const a = λ b → a

_×_ : Set → Set → Set
A × B = Σ A (const B)

uncurry : {A : Set} {B : A → Set} {C : Σ A B → Set} →
          ((x : A) (y : B x) → C (x , y)) →
          ((p : Σ A B) → C p)
uncurry f (x , y) = f x y

flip : {A B : Set} {C : A → B → Set} →
       ((x : A) (y : B) → C x y) → ((y : B) (x : A) → C x y)
flip f = λ x y → f y x

assoc : {A B C : Set} → (A × B) × C → A × (B × C)
assoc {A}{B}{C} = uncurry (flip λ z → uncurry λ x y → (x , (y , z)))

-- The code above is accepted if const is inlined in the definition of
-- _×_.
