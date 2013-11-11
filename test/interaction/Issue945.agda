-- Display whether or not the timeout was hit when using auto -l.
module Issue945 where

data ⊥ : Set where

¬_ : Set → Set
¬ A = A → ⊥

record ∃ {A : Set} (P : A → Set) : Set where
  constructor _,_
  field witness : A
        proof   : P witness

-- Exhaustive
lem₁ : ∀ {A : Set} (P : A → Set) (x : A) → (∀ x → ¬ P x) → (∀ x → P x) → ⊥
lem₁ A = {!-l -t 1!}

-- Timeout
lem₂ : ∀ {A} (P : A → Set) (x : A) → (∀ x → ¬ P x) → (∀ x → P x) → ∃ P → ⊥
lem₂ P a e = {!-l -t 1!}
