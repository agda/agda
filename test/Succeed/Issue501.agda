{-# OPTIONS --allow-unsolved-metas #-}
module Issue501 where

record ⊤ : Set where
  constructor tt

data _⊎_ (A : Set) (B : Set) : Set where
  inj₁ : (x : A) → A ⊎ B
  inj₂ : (y : B) → A ⊎ B

[_,_] : ∀ {A : Set} {B : Set} {C : A ⊎ B → Set} →
        ((x : A) → C (inj₁ x)) → ((x : B) → C (inj₂ x)) →
        ((x : A ⊎ B) → C x)
[ f , g ] (inj₁ x) = f x
[ f , g ] (inj₂ y) = g y

------------------------------------------------------------------------

Pow : Set → Set₁
Pow X = X → Set

-- Replacing /Pow I/ with /X → Set/ below makes the file load.

-- data _:=_ {I : Set}(A : Set)(i : I) : I → Set where
data _:=_ {I : Set}(A : Set)(i : I) : Pow I where
  ⟨_⟩ : (x : A) → (A := i) i

postulate
  S     : Set
  s     : S
  D     : Pow S → Pow S
  P     : Pow S
  m     : D P s
  _>>=_ : ∀ {A B s} → D A s → (∀ {s} → A s → D B s) → D B s

p : D P s
p = m >>= λ k → [ (λ { ⟨ x ⟩ → {!!} }) , {!!} ] {!!}
