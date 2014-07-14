
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} (i : Fin n) → Fin (suc n)

data _≤_ : ℕ → ℕ → Set where
  zero : ∀ {n}                → zero  ≤ n
  suc  : ∀ {m n} (le : m ≤ n) → suc m ≤ suc n

_<_ : ℕ → ℕ → Set
m < n = suc m ≤ n

toℕ : ∀ {n} → Fin n → ℕ
toℕ zero    = zero
toℕ (suc i) = suc (toℕ i)

fromℕ≤ : ∀ {m n} → m < n → Fin n
fromℕ≤ (suc zero)       = zero
fromℕ≤ (suc (suc m≤n)) = suc (fromℕ≤ (suc m≤n))

-- If we treat constructors as inert this fails to solve. Not entirely sure why.
fromℕ≤-toℕ : ∀ {m} (i : Fin m) (i<m : toℕ i < m) → fromℕ≤ i<m ≡ i
fromℕ≤-toℕ zero    (suc zero)       = refl
fromℕ≤-toℕ (suc i) (suc (suc m≤n)) = cong suc (fromℕ≤-toℕ i (suc m≤n))
