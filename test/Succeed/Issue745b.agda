
module _ where

-- This is all standard library stuff, inspect on steroids:

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

data Unit : Set where
  unit : Unit

Hidden : Set → Set
Hidden A = Unit → A

hide : {A : Set} {B : A → Set} →
       ((x : A) → B x) → ((x : A) → Hidden (B x))
hide f x unit = f x

reveal : {A : Set} → Hidden A → A
reveal f = f unit

data Reveal_is_ {A : Set} (x : Hidden A) (y : A) : Set where
  [_] : (eq : reveal x ≡ y) → Reveal x is y

inspect : {A : Set} {B : A → Set}
          (f : (x : A) → B x) (x : A) → Reveal (hide f x) is (f x)
inspect f x = [ refl ]

data ℕ : Set where
  zero : ℕ
  suc : ℕ -> ℕ


-- New stuff starts here:

data Wrap : ℕ -> Set where
  con : (n : ℕ) -> Wrap n

wrap : (n : ℕ) -> Wrap n
wrap zero    = con zero
wrap (suc x) = con (suc x)

bar-with : (n : ℕ)(v : Wrap n) -> Reveal (hide wrap n) is (wrap n) -> ℕ
bar-with n (con .n) r = zero

bar : (n : ℕ) -> ℕ
bar zero = zero
bar (suc n) = bar-with n (wrap n) (inspect wrap n)

-- I've manually desugared `bar' to make the error clearer, but the
-- following definition works correctly:
{-
bar : (n : ℕ) -> ℕ
bar zero = zero
bar (suc n) with wrap n | inspect wrap n
bar (suc ._) | con _    | r = zero
-}

foo : (n : ℕ) -> Wrap (bar n) -> ℕ
foo zero p = zero
foo (suc x) p with inspect bar x
foo (suc x) p | r = zero

-- The previous line gives the error:

-- ℕ != Wrap x of type Set
-- when checking that the type
-- (x : ℕ) (w : Reveal_is_ {ℕ} (hide {ℕ} {λ _ → ℕ} bar x) (bar x))
-- (p : Wrap (bar-with x (wrap x) w)) →
-- ℕ
-- of the generated with function is well-formed

-- In particular, notice that the type of `p' is incorrect, because an
-- occurrence of `inspect wrap x` has been turned into the variable w
-- (which corresponds to `inspect bar x`).

-- I think the correct desugaring of the with is as follows:

good-foo-with : (x : ℕ) -> Wrap (bar (suc x)) -> Reveal (hide bar x) is bar x -> ℕ
good-foo-with x w r = zero

good-foo : (n : ℕ) -> Wrap (bar n) -> ℕ
good-foo zero p = zero
good-foo (suc x) p = good-foo-with x p (inspect bar x)
