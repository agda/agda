{-# OPTIONS --rewriting #-}

data _≅_ {a} {A : Set a} (x : A) : ∀ {b} {B : Set b} → B → Set a where
   refl : x ≅ x

infix 4 _≡_
_≡_ : ∀ {ℓ} {A B : Set ℓ} → A → B → Set ℓ
x ≡ y = x ≅ y

module _ {a} (A : Set a) (x y : A) (foo : A → A) (eq : foo x ≡ y) where

  abstract
    x' : A
    x' = x
    y' : A
    y' = y
    foo' : A → A
    foo' = foo
    eq' : foo' x' ≡ y'
    eq' = eq


  {-# BUILTIN REWRITE _≡_ #-}
  {-# REWRITE eq' #-}

  lemma : foo' x' ≡ y'
  lemma = refl
