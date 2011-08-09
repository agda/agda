module RewriteAndWhere where

open import Common.Equality

sym : {A : Set}{a b : A} → a ≡ b → b ≡ a
sym refl = refl

data ℕ : Set where
  zero : ℕ

good : (a b : ℕ) → a ≡ b → b ≡ a
good a b eq with a | eq
... | .b | refl = foo
  where
    foo : b ≡ b
    foo = refl

mutual
  aux : (a b : ℕ)(w : ℕ) → w ≡ b → b ≡ w
  aux a b .b refl = foo
    where
     foo : b ≡ b
     foo = refl

  good₂ : (a b : ℕ) → a ≡ b → b ≡ a
  good₂ a b eq = aux a b a eq


bad : (a b : ℕ) → a ≡ b → b ≡ a
bad a b eq rewrite eq = foo
  where
    foo : b ≡ b
    foo rewrite sym eq = bar
      where
        bar : a ≡ a
        bar = refl
