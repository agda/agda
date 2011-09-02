{-# OPTIONS --type-in-type #-}
module Record where

infixr 2 _,_
record Σ (A : Set)(B : A → Set) : Set where
  constructor _,_
  field fst : A
        snd : B fst

open Σ

data ⊤ : Set where
  tt : ⊤

∃ : {A : Set}(B : A → Set) → Set
∃ B = Σ _ B

infix 10 _≡_

data _≡_ {A : Set}(a : A) : {B : Set} → B → Set where
  refl : a ≡ a

trans : ∀ {A B C}{a : A}{b : B}{c : C} → a ≡ b → b ≡ c → a ≡ c
trans refl p = p

sym : ∀ {A B}{a : A}{b : B} → a ≡ b → b ≡ a
sym refl = refl

resp : ∀ {A}{B : A → Set}{a a' : A} →
       (f : (a : A) → B a) → a ≡ a' → f a ≡ f a'
resp f refl = refl

Cat : Set
Cat =
  ∃ λ (Obj : Set) →
  ∃ λ (Hom : Obj → Obj → Set) →
  ∃ λ (id : ∀ X → Hom X X) →
  ∃ λ (_○_ : ∀ {X Y Z} → Hom Y Z → Hom X Y → Hom X Z) →
  ∃ λ (idl : ∀ {X Y}{f : Hom X Y} → id Y ○ f ≡ f) →
  ∃ λ (idr : ∀ {X Y}{f : Hom X Y} → f ○ id X ≡ f) →
  ∃ λ (assoc : ∀ {W X Y Z}{f : Hom W X}{g : Hom X Y}{h : Hom Y Z} →
                (h ○ g) ○ f ≡ h ○ (g ○ f)) →
  ⊤

Obj : (C : Cat) → Set
Obj C = fst C

Hom : (C : Cat) → Obj C → Obj C → Set
Hom C = fst (snd C)

id : (C : Cat) → ∀ X → Hom C X X
id C = fst (snd (snd C))

comp : (C : Cat) → ∀ {X Y Z} → Hom C Y Z → Hom C X Y → Hom C X Z
comp C = fst (snd (snd (snd C)))

idl : (C : Cat) → ∀ {X Y}{f : Hom C X Y} → comp C (id C Y) f ≡ f
idl C = fst (snd (snd (snd (snd C))))

idr : (C : Cat) → ∀ {X Y}{f : Hom C X Y} → comp C f (id C X) ≡ f
idr C = fst (snd (snd (snd (snd (snd C)))))

assoc : (C : Cat) → ∀ {W X Y Z}{f : Hom C W X}{g : Hom C X Y}{h : Hom C Y Z} →
        comp C (comp C h g) f ≡ comp C h (comp C g f)
assoc C = fst (snd (snd (snd (snd (snd (snd C))))))
