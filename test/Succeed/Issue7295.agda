module Issue7295 where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

postulate
  IsPreorder : {A : Set} → (A → A → Set) → (A → A → Set) → Set₁

module NatOrder where
  postulate
    _≤_ : Nat → Nat → Set
    ≤-isPreorder : IsPreorder _≡_ _≤_

module BoolOrder where
  postulate
    _≤_ : Bool → Bool → Set
    ≤-isPreorder : IsPreorder _≡_ _≤_

record HasPreorder (A : Set) (_≈_ : A → A → Set) : Set₁ where
  infix 4 _≤_
  field
    _≤_          : A → A → Set
    ≤-isPreorder : IsPreorder _≈_ _≤_

open HasPreorder ⦃...⦄ public

_∋_ : ∀ {a} (A : Set a) → A → A
A ∋ x = x

instance
  Nat-hasPreorder  = HasPreorder _ _ ∋ record {NatOrder}
  Bool-hasPreorder = HasPreorder _ _ ∋ record {BoolOrder}

data Dec (P : Set) : Set where
  yes : P → Dec P
  no : Dec P

case_of_ : ∀ {A B : Set} → A → (A → B) → B
case x of f = f x

record _⁇ (P : Set) : Set where
  constructor ⁇_
  field dec : Dec P

open _⁇ ⦃...⦄ public

¿_¿ : ∀ (X : Set) → ⦃ X ⁇ ⦄ → Dec X
¿ _ ¿ = dec

instance
  postulate Dec≤ : ∀ {n m : Nat} → (n ≤ m) ⁇

top : Set
top = Nat where  -- only fails in a `where` block
    IsGood : (new : Nat) → Set
    IsGood new = 1 ≤ new

    -- case/with over this works:
    -- checkGood : ∀ new → Dec (IsGood new)
    -- checkGood new = ¿ IsGood new ¿

    foo : ∀ new → Bool
    foo new = case ¿ IsGood new ¿ of λ where
      (yes _) → true
      no → true

    -- Used to be the case that postponing instance constraints based on
    -- whether the discrimination tree returned multiple results would
    -- cause 'with'-abstraction to fail (because the instance would only
    -- be solved *after* handling the with-problem). We're a bit more
    -- careful to only postpone when allowable now.

    bar : ∀ new → foo new ≡ true
    bar new with ¿ IsGood new ¿
    ... | yes _ = refl
    ... | no    = refl
