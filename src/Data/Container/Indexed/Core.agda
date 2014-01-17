------------------------------------------------------------------------
-- The Agda standard library
--
-- Indexed containers core
------------------------------------------------------------------------

module Data.Container.Indexed.Core where

open import Level
open import Data.Product
open import Relation.Unary

infix 5 _◃_/_

record Container {i o} (I : Set i) (O : Set o) (c r : Level) :
                 Set (i ⊔ o ⊔ suc c ⊔ suc r) where
  constructor _◃_/_
  field
    Command  : (o : O) → Set c
    Response : ∀ {o} → Command o → Set r
    next     : ∀ {o} (c : Command o) → Response c → I

-- The semantics ("extension") of an indexed container.

⟦_⟧ : ∀ {i o c r ℓ} {I : Set i} {O : Set o} → Container I O c r →
      Pred I ℓ → Pred O _
⟦ C ◃ R / n ⟧ X o = Σ[ c ∈ C o ] ((r : R c) → X (n c r))

------------------------------------------------------------------------
-- All and any

module _ {i o c r ℓ} {I : Set i} {O : Set o}
         (C : Container I O c r) {X : Pred I ℓ} where

  -- All.

  □ : ∀ {ℓ′} → Pred (Σ I X) ℓ′ → Pred (Σ O (⟦ C ⟧ X)) _
  □ P (_ , _ , k) = ∀ r → P (_ , k r)

  -- Any.

  ◇ : ∀ {ℓ′} → Pred (Σ I X) ℓ′ → Pred (Σ O (⟦ C ⟧ X)) _
  ◇ P (_ , _ , k) = ∃ λ r → P (_ , k r)
