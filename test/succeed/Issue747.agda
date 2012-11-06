-- {-# OPTIONS -v tc.inj:100 #-}
-- Andreas, 2012-11-06, issue raised by Guillaume Brunerie
module Issue747 where

data ℕ : Set where
  O : ℕ
  S : ℕ → ℕ

record Σ (A : Set) (P : A → Set) : Set where
  field
    π₁ : A
    π₂ : P π₁

data _≡_ {A : Set} : A → A → Set where
  refl : (a : A) → a ≡ a

is-contr : Set → Set
is-contr A = Σ A (λ x → ((y : A) → y ≡ x))

is-hlevel : (n : ℕ) → (Set → Set)
is-hlevel O     A = is-contr A
is-hlevel (S n) A = (x y : A) → is-hlevel n (x ≡ y)
-- is-hlevel should be injective

postulate
  t : ℕ → Set → Set
  t-is-hlevel : {n : ℕ} {A : Set} → is-hlevel n (t n A)
  A : Set
  f : (n : ℕ) (B : Set) ⦃ x : is-hlevel n B ⦄ → Set

g : (n : ℕ) → Set
g n = f n (t n A) {- ⦃ t-is-hlevel {n} ⦄ -}
-- instance should be found (depends on is-hlevel being injective)

