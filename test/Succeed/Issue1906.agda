
open import Agda.Primitive

record Relation {a b} (A : Set a) (B : Set b) c : Set (a ⊔ b ⊔ lsuc c) where
  constructor mk
  field
    _∼_ : A → B → Set c

record Setoid a c : Set (lsuc (a ⊔ c)) where
  constructor mk
  field
    carrier  : Set a
    relation : Relation carrier carrier c

  open Relation relation public renaming (_∼_ to _≈_)

record HeytingAlgebra {a c}
         (setoid : Setoid a c)
         (_∧_ _∨_ : let open Setoid setoid in
                    carrier → carrier → carrier) :
         Set (a ⊔ c) where
  constructor laws
  open Setoid setoid

  field
    ∧-cong : ∀ {x₁ x₂ y₁ y₂} → x₁ ≈ x₂ → y₁ ≈ y₂ → (x₁ ∧ y₁) ≈ (x₂ ∧ y₂)
    ∨-cong : ∀ {x₁ x₂ y₁ y₂} → x₁ ≈ x₂ → y₁ ≈ y₂ → (x₁ ∨ y₁) ≈ (x₂ ∨ y₂)

infix 0 _⇒_

record _⇒_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  constructor mk
  field
    ⇒-fst : A → B

open _⇒_ public

infix 0 _⇔_
infixr 0 _,_

record _⇔_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    ⇔-fst : A ⇒ B
    ⇔-snd : B ⇒ A

open _⇔_ public

⇔-relation : ∀ {a b} → Relation (Set a) (Set b) (a ⊔ b)
⇔-relation = mk _⇔_

⇔-setoid : ∀ c → Setoid (lsuc c) c
⇔-setoid c = mk (Set c) ⇔-relation

infix 0 _∧_

record _∧_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    ∧-fst : A
    ∧-snd : B

open _∧_ public

infix 0 _∨_

data _∨_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  ∨-inl : A → (A ∨ B)
  ∨-inr : B → (A ∨ B)

heyting-algebra : ∀ {a} → HeytingAlgebra (⇔-setoid a) _∧_ (_∨_ {a})
heyting-algebra {a} = laws ∧-cong ∨-cong
  where
  open Setoid (⇔-setoid _) -- much faster if _ is replaced by a

  ∧-cong : ∀ {x₁ x₂ y₁ y₂} → x₁ ≈ x₂ → y₁ ≈ y₂ → (x₁ ∧ y₁) ≈ (x₂ ∧ y₂)
  ∧-cong x₁≈x₂ y₁≈y₂ =
    mk (λ x₁∧y₁ → ⇒-fst (⇔-fst x₁≈x₂) (∧-fst x₁∧y₁) , ⇒-fst (⇔-fst y₁≈y₂) (∧-snd x₁∧y₁)) ,
    mk (λ x₂∧y₂ → ⇒-fst (⇔-snd x₁≈x₂) (∧-fst x₂∧y₂) , ⇒-fst (⇔-snd y₁≈y₂) (∧-snd x₂∧y₂))

  ∨-cong : ∀ {x₁ x₂ y₁ y₂} → x₁ ≈ x₂ → y₁ ≈ y₂ → (x₁ ∨ y₁) ≈ (x₂ ∨ y₂)

  -- 1.1s
  ∨-cong {x₁} {x₂} {y₁} {y₂} x₁≈x₂ y₁≈y₂ =
    mk lemma₁ , mk lemma₂
    where
    lemma₁ : x₁ ∨ y₁ →  x₂ ∨ y₂
    lemma₁ (∨-inl x₁) = ∨-inl (⇒-fst (⇔-fst x₁≈x₂) x₁)
    lemma₁ (∨-inr y₁) = ∨-inr (⇒-fst (⇔-fst y₁≈y₂) y₁)
    lemma₂ : x₂ ∨ y₂ →  x₁ ∨ y₁
    lemma₂ (∨-inl x₂) = ∨-inl (⇒-fst (⇔-snd x₁≈x₂) x₂)
    lemma₂ (∨-inr y₂) = ∨-inr (⇒-fst (⇔-snd y₁≈y₂) y₂)

  -- -- 3.0s
  -- ∨-cong {x₁} {x₂} {y₁} {y₂} (x₁⇒x₂ , x₂⇒x₁) (y₁⇒y₂ , y₂⇒y₁) =
  --   mk lemma₁ , mk lemma₂
  --   where
  --   lemma₁ : x₁ ∨ y₁ →  x₂ ∨ y₂
  --   lemma₁ (∨-inl x₁) = ∨-inl (⇒-fst x₁⇒x₂ x₁)
  --   lemma₁ (∨-inr y₁) = ∨-inr (⇒-fst y₁⇒y₂ y₁)
  --   lemma₂ : x₂ ∨ y₂ →  x₁ ∨ y₁
  --   lemma₂ (∨-inl x₂) = ∨-inl (⇒-fst x₂⇒x₁ x₂)
  --   lemma₂ (∨-inr y₂) = ∨-inr (⇒-fst y₂⇒y₁ y₂)

  -- -- 0.4s
  -- ∨-cong {x₁} {x₂} {y₁} {y₂} (mk x₁→x₂ , mk x₂→x₁) (mk y₁→y₂ , mk y₂→y₁) =
  --   mk lemma₁ , mk lemma₂
  --   where
  --   lemma₁ : x₁ ∨ y₁ →  x₂ ∨ y₂
  --   lemma₁ (∨-inl x₁) = ∨-inl (x₁→x₂ x₁)
  --   lemma₁ (∨-inr y₁) = ∨-inr (y₁→y₂ y₁)
  --   lemma₂ : x₂ ∨ y₂ →  x₁ ∨ y₁
  --   lemma₂ (∨-inl x₂) = ∨-inl (x₂→x₁ x₂)
  --   lemma₂ (∨-inr y₂) = ∨-inr (y₂→y₁ y₂)
