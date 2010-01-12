module Functor where

record IsEquivalence {A : Set} (_≈_ : A → A → Set) : Set where
  field
    refl  : ∀ {x} → x ≈ x
    sym   : ∀ {i j} → i ≈ j → j ≈ i
    trans : ∀ {i j k} → i ≈ j → j ≈ k → i ≈ k

record Setoid : Set₁ where
  infix 4 _≈_
  field
    Carrier       : Set
    _≈_           : Carrier → Carrier → Set
    isEquivalence : IsEquivalence _≈_

  open IsEquivalence isEquivalence public

infixr 0 _⟶_

record _⟶_ (From To : Setoid) : Set where
  infixl 5 _⟨$⟩_
  field
    _⟨$⟩_ : Setoid.Carrier From → Setoid.Carrier To
    cong  : ∀ {x y} →
            Setoid._≈_ From x y → Setoid._≈_ To (_⟨$⟩_ x) (_⟨$⟩_ y)

open _⟶_ public

id : ∀ {A} → A ⟶ A
id = record { _⟨$⟩_ = λ x → x; cong = λ x≈y → x≈y }

infixr 9 _∘_

_∘_ : ∀ {A B C} → B ⟶ C → A ⟶ B → A ⟶ C
f ∘ g = record
  { _⟨$⟩_ = λ x → f ⟨$⟩ (g ⟨$⟩ x)
  ; cong  = λ x≈y → cong f (cong g x≈y)
  }

_⇨_ : (To From : Setoid) → Setoid
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

record Functor (F : Setoid → Setoid) : Set₁ where
  field
    map : ∀ {A B} → (A ⇨ B) ⟶ (F A ⇨ F B)

    identity : ∀ {A} →
      let open Setoid (F A ⇨ F A) in
      map ⟨$⟩ id ≈ id

    composition : ∀ {A B C} (f : B ⟶ C) (g : A ⟶ B) →
      let open Setoid (F A ⇨ F C) in
      map ⟨$⟩ f ∘ g ≈ (map ⟨$⟩ f) ∘ (map ⟨$⟩ g)
