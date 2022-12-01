
module _ where

record Structure : Set1 where
  infixl 20 _×_
  infix   8 _⟶_
  infixl 20 _,_
  infixr 40 _∘_

  infix 5 _~_

  field
    Type : Set
    _×_  : Type → Type → Type

    _⟶_ : Type → Type → Set
    _∘_ : ∀ {X Y Z} → Y ⟶ Z → X ⟶ Y → X ⟶ Z
    _,_ : ∀ {X A B} → X ⟶ A → X ⟶ B → X ⟶ A × B
    π₁  : ∀ {A B} → A × B ⟶ A
    π₂  : ∀ {A B} → A × B ⟶ B
    Op3 : ∀ {X} → X × X × X ⟶ X

    _~_ : ∀ {X Y} → X ⟶ Y → X ⟶ Y → Set

record Map {{C : Structure}} {{D : Structure}} : Set1 where
  open Structure {{...}}
  field
    Ty⟦_⟧ : Structure.Type C → Structure.Type D
    Tm⟦_⟧ : ∀ {X A} → X ⟶ A → Ty⟦ X ⟧ ⟶ Ty⟦ A ⟧

    ×-inv : ∀ {X A} → Ty⟦ X ⟧ × Ty⟦ A ⟧ ⟶ Ty⟦ X × A ⟧

    ⟦Op3⟧ : ∀ {X : Structure.Type C} → Tm⟦ Op3 {X = X} ⟧ ∘ ×-inv ∘ (×-inv ∘ (π₁ ∘ π₁ , π₂ ∘ π₁) , π₂) ~ Op3
