-- Andreas, 2022-03-09, issue #5819, reported by Zilin Chen
--
-- This test uncovered an unsound optimization (8e0fca895b9c6740d9d6c1751ed1e0ecefe63473)
-- in the termination checker which replaced a (stripAllProjections . normalize)
-- by a (iteratively reduce . stripAllProjections).
-- Those reductions on now ill-formed terms triggered the __IMPOSSIBLE__:
-- Incomplete pattern matching when applying Issue5819.dl-iso

open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma renaming (fst to proj₁; snd to proj₂)

data ⊥ : Set where

∃ : {A : Set} (B : A → Set) → Set
∃ B = Σ _ B

_×_ : (A B : Set) → Set
A × B = Σ A λ _ → B

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

_≢_ : {A : Set} (x y : A) → Set
x ≢ y = x ≡ y → ⊥

record Inverse (A B : Set) : Set where
  field
    f         : A → B
    f⁻¹       : B → A
    inverse   : ∀ x → f (f⁻¹ x) ≡ x
open Inverse

data DList : Set
Fresh : (a : ℕ) → (l : DList) → Set

data DList where
  dnil  : DList
  dcons : (a : ℕ) → (l : DList) → Fresh a l → DList

Fresh a dnil = ⊤
Fresh a (dcons b l _) = (a ≢ b) × Fresh a l

data List′ : Set where
  nil′  : List′
  cons′ : ℕ → List′ → List′

Fresh′ : ℕ → List′ → Set
Fresh′ a nil′ = ⊤
Fresh′ a (cons′ b l) = (a ≢ b) × Fresh′ a l

AllFresh : List′ → Set
AllFresh nil′ = ⊤
AllFresh (cons′ a l) = Fresh′ a l × AllFresh l

data DList′ : List′ → Set → Set₁ where
  dnil′  : DList′ nil′ ⊤
  dcons′ : ∀{l}{prf} → (a : ℕ) → DList′ l prf → DList′ (cons′ a l) (Fresh′ a l × prf)


data DList″ : Set where
  dl″ : (l : List′) → AllFresh l → DList″

undl″-l : DList″ → List′
undl″-l (dl″ l _) = l

undl″-p : DList″ → ∃ AllFresh
undl″-p (dl″ l p) = l , p

-- dl-iso : DList ↔ DList″
dl-iso : Inverse DList DList″
-- f-dl-iso : DList → DList″
-- g-dl-iso : DList″ → DList
-- inverse-dl-iso : ∀ x → f-dl-iso (g-dl-iso x) ≡ x

Fresh→Fresh′ : ∀{a}{l}{l″}
             → (f dl-iso l ≡ l″)
             → Fresh a l
             → Fresh′ a (undl″-l l″)

Fresh→AllFresh : ∀{a}{l}{l″}
               → (f dl-iso l ≡ l″)
               → Fresh a l
               → AllFresh (undl″-l l″)

All/Fresh′→Fresh : ∀{a}{l}{l″}
       → (l ≡ f⁻¹ dl-iso l″)
       → Fresh′ a (undl″-l l″) × AllFresh (undl″-l l″)
       → Fresh a l

f dl-iso dnil = dl″ nil′ tt
f dl-iso (dcons a l p)
  = dl″ (cons′ a (undl″-l (f dl-iso l)))
        ((Fresh→Fresh′ {l = l}{l″ = f dl-iso l} refl p) ,
         (Fresh→AllFresh {a = a}{l = l}{l″ = f dl-iso l} refl p))

f⁻¹ dl-iso (dl″ nil′ p) = dnil
f⁻¹ dl-iso (dl″ (cons′ a l′) p)
  = dcons a (f⁻¹ dl-iso (dl″ l′ (proj₂ p)))
            (All/Fresh′→Fresh {l″ = dl″ l′ (proj₂ p)} refl p)

-- Can't do any further, otherwise an Agda bug occurs.
inverse dl-iso x = invˡ
  where
  invˡ : ∀{x} → f dl-iso (f⁻¹ dl-iso x) ≡ x
  invˡ {dl″ nil′ _} = refl
  invˡ {dl″ (cons′ a l) p} rewrite invˡ {dl″ l {!!}} = {!!}  -- add "rewrite invˡ {dl″ l ?}" (w/o quotes) to the left of the = sign and C-c C-l

Fresh→Fresh′ {a} {dnil} eq p rewrite sym eq = tt
Fresh→Fresh′ {a} {dcons a₁ l x} eq p rewrite sym eq
  = proj₁ p ,  Fresh→Fresh′ {l″ = f dl-iso l} refl (proj₂ p)

Fresh→AllFresh {l = dnil} eq p rewrite sym eq = tt
Fresh→AllFresh {l = dcons a l x} eq p rewrite sym eq
  = (Fresh→Fresh′ {l″ = f dl-iso l} refl x) , Fresh→AllFresh {a = a}{l = l}{l″ = f dl-iso l} refl x

All/Fresh′→Fresh {a} {l″ = dl″ nil′ x} eq p rewrite eq = tt
All/Fresh′→Fresh {a} {l″ = dl″ (cons′ b l) x} eq p rewrite eq
  = (proj₁ (proj₁ p)) , {!All/Fresh′→Fresh!}  -- put "All/Fresh′→Fresh" in the hole and C-c C-r

-- WAS: internal error in reduction machinery
-- SHOULD: fail with termination error
