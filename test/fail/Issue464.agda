{-# OPTIONS --universe-polymorphism #-}

module Issue464 where

open import Common.Level

data _×_ {a b}(A : Set a)(B : Set b) : Set (a ⊔ b) where
  _,_ : A → B → A × B

data ⊥ : Set where
record ⊤ : Set where

-----------------------------------

data nonSP : Set1 where
  ι : nonSP
  δ : (A : Set) -> nonSP -> nonSP

⟦_⟧ : nonSP -> (Set × ⊤) -> Set
⟦ ι ⟧ UT = ⊤
⟦ (δ A γ) ⟧ (U , T) = (U -> A) × ⟦ γ ⟧ (U , T)

data U (γ : nonSP) : Set where
  intro : ⟦ γ ⟧ (U γ , _) -> U γ
-- the positivity checker objects (as it should) if "(Set × ⊤)" is changed to "Set"
-- in the type of ⟦_⟧ and "(U γ , _)" is changed accordingly to "U γ".

bad : Set
bad = U (δ ⊥ ι) -- constructor in : (bad -> ⊥) -> bad

p : bad -> ⊥
p (intro (x , _)) = x (intro (x , _))

absurd : ⊥
absurd = p (intro (p , _))
