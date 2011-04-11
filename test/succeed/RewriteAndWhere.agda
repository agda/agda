
module RewriteAndWhere where

data _≡_ {A : Set}(x : A) : A → Set where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

sym : ∀ {A}{a b : A} → a ≡ b → b ≡ a
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
