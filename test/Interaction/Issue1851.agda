-- Adapted from an example reported by John Leon

-- It seems that the change reported in the issue was caused by the
-- commit 344296cf06cedd13736e50bb53e63217d9f19ecf.

-- Using `C-c C-,` in the first goal, master and 2.4.2.5 have different
-- behaviours. In master, the type of `a` is not normalised

-- Goal: n ≡ n + zero
-- ————————————————————————————————————————————————————————————
-- a : flip _≡_ (n + zero) n
-- n : ℕ

-- but in 2.4.2.5, the type of `a` is full normalised

-- Goal: n ≡ n + zero
-- ————————————————————————————————————————————————————————————
-- a : n ≡ n + 0
-- n : ℕ

infix 4 _≡_
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

cong : ∀ {A B : Set} (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

REL : Set → Set → Set₁
REL A B = A → B → Set

flip : {A B : Set} {C : A → B → Set₁} →
       ((x : A) (y : B) → C x y) → ((y : B) (x : A) → C x y)
flip f = λ y x → f x y
{-# NOINLINE flip #-}

infixr 4 _⇒_
_⇒_ : {A B : Set} → REL A B → REL A B → Set
P ⇒ Q = ∀ {i j} → P i j → Q i j

Sym : {A B : Set} → REL A B → REL B A → Set
Sym P Q = P ⇒ flip Q

Symmetric : {A : Set} → REL A A → Set
Symmetric _∼_ = Sym _∼_ _∼_

sym : {A : Set} → Symmetric (_≡_ {A = A})
sym refl = refl

data ℕ : Set where
  zero : ℕ
  suc  : (n : ℕ) → ℕ

infixl 6 _+_
_+_ : ℕ → ℕ → ℕ
zero  + m = m
suc n + m = suc (n + m)

n+0=n : (n : ℕ) → n + zero ≡ n
n+0=n zero    = refl
n+0=n (suc n) = cong suc (n+0=n (n))

m+Sn : (m n : ℕ) → m + suc n ≡ suc (m + n)
m+Sn zero    n = refl
m+Sn (suc m) n = cong suc (m+Sn m n)

+comm : (m n : ℕ) → m + n ≡ n + m
+comm zero    n =
  let a = sym (n+0=n n)
  in {!!}
+comm (suc m) n =
  let a = cong suc (+comm m n)
      b = sym (m+Sn n m)
  in {!!}
