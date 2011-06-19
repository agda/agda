{-# OPTIONS --universe-polymorphism #-}

module UniversePolymorphicFunctor where

postulate
  Level : Set
  zero : Level
  suc  : (i : Level) → Level
  _⊔_ : Level → Level → Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO zero  #-}
{-# BUILTIN LEVELSUC  suc   #-}
{-# BUILTIN LEVELMAX  _⊔_   #-}

infixl 6 _⊔_


record IsEquivalence {a ℓ} {A : Set a}
                     (_≈_ : A → A → Set ℓ) : Set (a ⊔ ℓ) where
  field
    refl  : ∀ {x} → x ≈ x
    sym   : ∀ {i j} → i ≈ j → j ≈ i
    trans : ∀ {i j k} → i ≈ j → j ≈ k → i ≈ k

record Setoid c ℓ : Set (suc (c ⊔ ℓ)) where
  infix 4 _≈_
  field
    Carrier       : Set c
    _≈_           : Carrier → Carrier → Set ℓ
    isEquivalence : IsEquivalence _≈_

  open IsEquivalence isEquivalence public

infixr 0 _⟶_

record _⟶_ {f₁ f₂ t₁ t₂}
           (From : Setoid f₁ f₂) (To : Setoid t₁ t₂) :
           Set (f₁ ⊔ f₂ ⊔ t₁ ⊔ t₂) where
  infixl 5 _⟨$⟩_
  field
    _⟨$⟩_ : Setoid.Carrier From → Setoid.Carrier To
    cong  : ∀ {x y} →
            Setoid._≈_ From x y → Setoid._≈_ To (_⟨$⟩_ x) (_⟨$⟩_ y)

open _⟶_ public

id : ∀ {a₁ a₂} {A : Setoid a₁ a₂} → A ⟶ A
id = record { _⟨$⟩_ = λ x → x; cong = λ x≈y → x≈y }

infixr 9 _∘_

_∘_ : ∀ {a₁ a₂} {A : Setoid a₁ a₂}
        {b₁ b₂} {B : Setoid b₁ b₂}
        {c₁ c₂} {C : Setoid c₁ c₂} →
      B ⟶ C → A ⟶ B → A ⟶ C
f ∘ g = record
  { _⟨$⟩_ = λ x → f ⟨$⟩ (g ⟨$⟩ x)
  ; cong  = λ x≈y → cong f (cong g x≈y)
  }

_⇨_ : ∀ {f₁ f₂ t₁ t₂} → Setoid f₁ f₂ → Setoid t₁ t₂ → Setoid _ _
From ⇨ To = record
  { Carrier       = From ⟶ To
  ; _≈_           = λ f g → ∀ {x y} → x ≈₁ y → f ⟨$⟩ x ≈₂ g ⟨$⟩ y
  ; isEquivalence = record
    { refl  = λ {f} → cong f
    ; sym   = λ f∼g x∼y → To.sym (f∼g (From.sym x∼y))
    ; trans = λ f∼g g∼h x∼y → To.trans (f∼g From.refl) (g∼h x∼y)
    }
  }
  where
  open module From = Setoid From using () renaming (_≈_ to _≈₁_)
  open module To   = Setoid To   using () renaming (_≈_ to _≈₂_)

record Functor {f₁ f₂ f₃ f₄}
               (F : Setoid f₁ f₂ → Setoid f₃ f₄) :
               Set (suc (f₁ ⊔ f₂) ⊔ f₃ ⊔ f₄) where
  field
    map : ∀ {A B} → (A ⇨ B) ⟶ (F A ⇨ F B)

    identity : ∀ {A} →
      let open Setoid (F A ⇨ F A) in
      map ⟨$⟩ id ≈ id

    composition : ∀ {A B C} (f : B ⟶ C) (g : A ⟶ B) →
      let open Setoid (F A ⇨ F C) in
      map ⟨$⟩ (f ∘ g) ≈ (map ⟨$⟩ f) ∘ (map ⟨$⟩ g)
