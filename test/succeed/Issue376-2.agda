-- Christian Sattler, 2013-12-31
-- Testing eta-expansion of bound record metavars, as implemented by Andreas.
module Issue376-2 where

{- A simple example. -}
module example-0 {A B : Set} where
  record Prod : Set where
    constructor _,_
    field
      fst : A
      snd : B

  module _ (F : (Prod → Set) → Set) where
    q : (∀ f → F f) → (∀ f → F f)
    q h _ = h (λ {(a , b) → _})

{- A more complex, real-life-based example: the dependent
   generalization of (A × B) × (C × D) ≃ (A × C) × (B × D). -}
module example-1 where
  record Σ (A : Set) (B : A → Set) : Set where
    constructor _,_
    field
      fst : A
      snd : B fst

  postulate
    _≃_ : (A B : Set) → Set

  Σ-interchange-Type =
    {A : Set} {B C : A → Set} {D : (a : A) → B a → C a → Set}
      → Σ (Σ A B) (λ {(a , b) → Σ (C a) (λ c → D a b c)})
      ≃ Σ (Σ A C) (λ {(a , c) → Σ (B a) (λ b → D a b c)})

  postulate
    Σ-interchange : Σ-interchange-Type

  {- Can the implicit arguments to Σ-interchange
     be inferred from the global type? -}
  Σ-interchange' : Σ-interchange-Type
  Σ-interchange' = Σ-interchange
