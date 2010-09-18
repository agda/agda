{- 2010-09-17 a small case study to test irrelevance -}

module IrrelevanceCaseStudyPartialFunctions where

data _≡_ {A : Set}(a : A) : A → Set where
  refl : a ≡ a

record ⊤ : Set where

record Sigma (A : Set)(B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst

syntax Sigma A (λ x → B) = Σ x ∈ A , B

data Subset (A : Set)(P : A → Set) : Set where
  _#_ : (elem : A) → .(P elem) → Subset A P

elimSubset : ∀ {A C : Set} {P} →
             Subset A P → ((a : A) → .(P a) → C) → C
elimSubset (a # p) k = k a p

syntax Subset A (λ x → P) = ⁅ x ∈ A ∣ P ⁆

elem : {A : Set}{P : A → Set} → ⁅ x ∈ A ∣ P x ⁆ → A
elem (x # p) = x

elim₂ : ∀ {A C : Set} {P Q : A → Set} →
        Subset A (λ x → Sigma (P x) (λ _ → Q x)) →
        ((a : A) → .(P a) → .(Q a) → C) → C
elim₂ (a # (p , q)) k = k a p q


record _⇀_ (A B : Set) : Set1 where
  constructor mkParFun
  field
    dom : A → Set
    _′_ : ⁅ x ∈ A ∣ dom x ⁆ → B

open _⇀_ public

syntax mkParFun dom f = f ↾ dom

pure : {A B : Set} → (A → B) → A ⇀ B
pure f = record { dom = λ x → ⊤ ; _′_ = λ a → f (elem a) }

_∘_ : {A B C : Set} → (B ⇀ C) → (A ⇀ B) → A ⇀ C
(g ↾ Q) ∘ (f ↾ P) = gf ↾ QP where
  QP : _ → Set
  QP x             = Σ x∈P ∈ P x , Q (f (x # x∈P))
  gf : Subset _ QP → _
  gf (x # (p , q)) = g (f (x # p) # q)

_⊑_ : {A B : Set} → (f f' : A ⇀ B) → Set
(f ↾ P) ⊑ (f' ↾ P') =
  Σ φ ∈ (∀ {x} → P x → P' x) ,
    (∀ {x} (p : P x) → f (x # p) ≡ f' (x # φ p))
