-- Andreas, 2015-06-24

{-# OPTIONS --guardedness #-}

-- {-# OPTIONS -v tc.with.strip:20 #-}

module _ where

open import Common.Equality
open import Common.Product

module SynchronousIO (I O : Set) where

  F : Set → Set
  F S = I → O × S

  record SyncIO : Set₁ where
    field
      St : Set
      tr : St → F St

  module Eq (A₁ A₂ : SyncIO) where

    open SyncIO A₁ renaming (St to S₁; tr to tr₁)
    open SyncIO A₂ renaming (St to S₂; tr to tr₂)

    record BiSim (s₁ : S₁) (s₂ : S₂) : Set where
      coinductive
      field
        force : ∀ (i : I) →
          let (o₁ , t₁) = tr₁ s₁ i
              (o₂ , t₂) = tr₂ s₂ i
          in  o₁ ≡ o₂ × BiSim t₁ t₂

  module Trans (A₁ A₂ A₃ : SyncIO) where

    open SyncIO A₁ renaming (St to S₁; tr to tr₁)
    open SyncIO A₂ renaming (St to S₂; tr to tr₂)
    open SyncIO A₃ renaming (St to S₃; tr to tr₃)

    open Eq A₁ A₂ renaming (BiSim to _₁≅₂_; module BiSim to B₁₂)
    open Eq A₂ A₃ renaming (BiSim to _₂≅₃_; module BiSim to B₂₃)
    open Eq A₁ A₃ renaming (BiSim to _₁≅₃_; module BiSim to B₁₃)

    open B₁₂ renaming (force to force₁₂)
    open B₂₃ renaming (force to force₂₃)
    open B₁₃ renaming (force to force₁₃)

    transitivity : ∀{s₁ s₂ s₃} (p : s₁ ₁≅₂ s₂) (p' : s₂ ₂≅₃ s₃) → s₁ ₁≅₃ s₃
    force₁₃ (transitivity p p') i with force₁₂ p i | force₂₃ p' i
    force₁₃ (transitivity p p') i | (q , r) | (q' , r') = trans q q' , transitivity r r'

-- with-clause stripping failed for projections from module applications
-- should work now
