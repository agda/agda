
module Issue739 where

record ⊤ : Set where
  constructor tt

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst

uncurry : {A : Set} {B : A → Set} →
          ((x : A) → B x → Set) →
          Σ A B → Set
uncurry f (x , y) = f x y

data U : Set₁

El : U → Set

infixl 5 _▻_

data U where
  ε   : U
  _▻_ : (u : U) → (El u → Set) → U

El ε       = ⊤
El (u ▻ P) = Σ (El u) P

Id : ∀ u → (El u → Set) → El u → Set
Id u P = P

-- Type-checks:

works : U
works =
  ε
  ▻ (λ _ → ⊤)
  ▻ (λ { (_ , _) → ⊤ })

-- Type-checks:

works′ : U
works′ =
  ε
  ▻ (λ _ → ⊤)
  ▻ Id (_ ▻ _) (λ { (_ , _) → ⊤ })

-- Type-checks:

works″ : U
works″ =
  ε
  ▻ (λ _ → ⊤)
  ▻ Id _ (uncurry λ _ _ → ⊤)

-- Type-checks:

works‴ : U
works‴ =
  ε
  ▻ (λ _ → ⊤)
  ▻ Id _ const-⊤
  where
  const-⊤ : _ → _
  const-⊤ (_ , _) = ⊤

-- Type-checks:

works⁗ : U
works⁗ =
  ε
  ▻ (λ _ → ⊤)
  ▻ Id _ const-⊤
  where
  const-⊤ : _ → _
  const-⊤ = λ { (_ , _) → ⊤ }

-- Type-checks:

works′́ : U
works′́ =
  ε
  ▻ (λ _ → ⊤)
  ▻ Id _ (λ { _ → ⊤ })

-- Doesn't type-check (but I want to write something like this):

fails : U
fails =
  ε
  ▻ (λ _ → ⊤)
  ▻ Id _ (λ { (_ , _) → ⊤ })

-- Given all the working examples I'm led to believe that there is
-- something wrong with pattern-matching lambdas. Please correct me if
-- I'm wrong.

-- Andreas, 2012-10-29 should work now.
