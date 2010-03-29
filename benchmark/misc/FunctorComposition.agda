module FunctorComposition where

open import Functor as F

compose : {F₁ F₂ : Setoid → Setoid} →
          Functor F₁ → Functor F₂ → Functor (λ A → F₁ (F₂ A))
compose {F₁} {F₂} FF₁ FF₂ = record
  { map      = map FF₁ ∘ map FF₂
  ; identity = λ {A} →
      trans (F₁ (F₂ A) ⇨ F₁ (F₂ A))
            {i = map FF₁ ⟨$⟩ (map FF₂ ⟨$⟩ id)}
            {j = map FF₁ ⟨$⟩ id}
            {k = id}
            (cong (map FF₁) (identity FF₂))
            (identity FF₁)
  ; composition = λ {A B C} f g →
      trans (F₁ (F₂ A) ⇨ F₁ (F₂ C))
            {i = map FF₁ ⟨$⟩ (map FF₂ ⟨$⟩ (f ∘ g))}
            {j = map FF₁ ⟨$⟩ ((map FF₂ ⟨$⟩ f) ∘ (map FF₂ ⟨$⟩ g))}
            {k = (map FF₁ ⟨$⟩ (map FF₂ ⟨$⟩ f)) ∘
                 (map FF₁ ⟨$⟩ (map FF₂ ⟨$⟩ g))}
            (cong (map FF₁) (composition FF₂ f g))
            (composition FF₁ (map FF₂ ⟨$⟩ f) (map FF₂ ⟨$⟩ g))
  }
  where
  open Setoid
  open F.Functor
