
record ∃ {A : Set} (B : A → Set) : Set where
  field
    fst : A
    snd : B fst

data ⊥ : Set where

infix 3 ¬_

¬_ : Set → Set
¬ P = P → ⊥

infixr 1 _⊎_

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

⊎-map : ∀ {A₁ A₂ B₁ B₂ : Set} →
        (A₁ → A₂) → (B₁ → B₂) → A₁ ⊎ B₁ → A₂ ⊎ B₂
⊎-map f g (inj₁ x) = inj₁ (f x)
⊎-map f g (inj₂ y) = inj₂ (g y)

record Raw-monad (M : Set → Set) : Set₁ where
  constructor mk
  infixl 5 _>>=_
  field
    return : ∀ {A} → A → M A
    _>>=_  : ∀ {A B} → M A → (A → M B) → M B

  map : ∀ {A B} → (A → B) → M A → M B
  map f x = x >>= λ x → return (f x)

open Raw-monad ⦃ … ⦄

-- Id is included in order to make run overloaded.

record Id (A : Set) : Set where
  field
    run : A

open Id

infix 3 ¬¬_

record ¬¬_ (A : Set) : Set where
  field
    run : ¬ ¬ A

open ¬¬_

instance

  double-negation-monad : Raw-monad ¬¬_
  run (Raw-monad.return double-negation-monad x)   = λ f → f x
  run (Raw-monad._>>=_  double-negation-monad x f) =
    λ ¬b → run x (λ a → run (f a) ¬b)

excluded-middle : {A : Set} → ¬¬ (A ⊎ ¬ A)
run excluded-middle ¬[a⊎¬a] = ¬[a⊎¬a] (inj₂ λ a → ¬[a⊎¬a] (inj₁ a))

postulate

  A    : Set
  P    : Set → Set
  _⇓_  : P A → A → Set
  _⇑   : P A → Set
  ¬⇓→⇑ : {x : P A} → ¬ (∃ λ y → x ⇓ y) → x ⇑

¬¬[⇓⊎⇑] : (x : P A) → ¬ ¬ ((∃ λ y → x ⇓ y) ⊎ x ⇑)
¬¬[⇓⊎⇑] x = run (map (⊎-map (λ x → x) ¬⇓→⇑) excluded-middle)
