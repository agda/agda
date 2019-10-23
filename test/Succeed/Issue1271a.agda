
-- Empty, unit and equality.

⊥ = (X : Set) → X
⊤ = (X : Set) → X → X

data _≡_ {l}{A : Set l}(x : A) : A → Set l where
  <> : x ≡ x

-- The fixpoint of the identity functor as a data definition.

module Data where

  data μId : Set where
    In : μId → μId

-- μId can be proved empty. Here are both a direct proof and one that
-- relies on the eliminator for μId.

  ¬μId : μId → ⊥
  ¬μId (In x) = ¬μId x

  μId-elim : ∀ {l}(P : μId → Set l) → (∀ x → P x → P (In x)) → ∀ x → P x
  μId-elim P m (In x) = m x (μId-elim P m x)

  ¬Id' : μId → ⊥
  ¬Id' = μId-elim (λ _ → ⊥) (λ _ p → p)

-- To prove ∀ x → ¬ (x ≡ In x) it is enough to call ¬μId (or ¬μId'): the
-- equality proof is not inspected.

  ¬id≡In-empty : ∀ {x} → x ≡ In x → ⊥
  ¬id≡In-empty {x} _ = ¬μId x -- or ¬Id' x

-- Alternatively, one could use an absurd pattern which relies on the
-- presence of a cycle.

  ¬id≡In-pm : ∀ {x} → x ≡ In x → ⊥
  ¬id≡In-pm ()

-- The case of inductive records is a bit different. Here is the fixpoint
-- of the identity functor as an inductive record definition.

module Record where

  record μId : Set where
    inductive
    constructor In
    field       Out : μId
  open μId

  -- It does not seem possible to prove Record.μId empty, as Agda does not
  -- consider the following definitions as terminating.
  -- EDIT: it does now.

  ¬μId : μId → ⊥
  ¬μId (In x) = ¬μId x

  μId-elim : ∀ {l}(P : μId → Set l) → (∀ x → P x → P (In x)) → ∀ x → P x
  μId-elim P m (In x) = m x (μId-elim P m x)

  ¬Id' : μId → ⊥
  ¬Id' = μId-elim (λ _ → ⊥) (λ _ p → p)

  ¬id≡In-empty : ∀ {x} → x ≡ In x → ⊥
  ¬id≡In-empty {x} _ = ¬μId x -- or ¬Id' x

-- However, we can still use an absurd pattern as in Data.¬id≡In-pm.

  ¬id≡In-pm : ∀ {x} → x ≡ In x → ⊥
  ¬id≡In-pm ()

-- This should not be possible.
