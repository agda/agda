------------------------------------------------------------------------
-- Some properties about subsets
------------------------------------------------------------------------

module Data.Fin.Subset.Props where

open import Data.Nat
open import Data.Bool
open import Data.Bool.Properties
open import Data.Vec hiding (_∈_)
open import Data.Vec.Properties
open import Data.Empty
open import Function
open import Data.Fin
open import Data.Fin.Subset
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Algebra
import Level
open import Algebra.FunctionProperties
open import Algebra.Structures

------------------------------------------------------------------------
-- Constructor mangling

drop-there : ∀ {s n x} {p : Subset n} → suc x ∈ s ∷ p → x ∈ p
drop-there (there x∈p) = x∈p

drop-∷-⊆ : ∀ {n s₁ s₂} {p₁ p₂ : Subset n} → s₁ ∷ p₁ ⊆ s₂ ∷ p₂ → p₁ ⊆ p₂
drop-∷-⊆ p₁s₁⊆p₂s₂ x∈p₁ = drop-there $ p₁s₁⊆p₂s₂ (there x∈p₁)

drop-∷-Empty : ∀ {n s} {p : Subset n} → Empty (s ∷ p) → Empty p
drop-∷-Empty ¬¬∅ (x , x∈p) = ¬¬∅ (suc x , there x∈p)

------------------------------------------------------------------------
-- Basic properties

x∉∅ : ∀ {n} {x : Fin n} → x ∉ ∅
x∉∅ {x = zero} () 
x∉∅ {x = suc x} (there p) = x∉∅ p

x∈⁅x⁆ : ∀ {n} {x : Fin n} → x ∈ ⁅ x ⁆
x∈⁅x⁆ {zero} {()}
x∈⁅x⁆ {suc n} {zero} = here
x∈⁅x⁆ {suc n} {suc i} = there x∈⁅x⁆

x∈full : ∀ {n} {x : Fin n} → x ∈ full
x∈full {x = zero} = here
x∈full {x = suc x} = there (x∈full {x = x})

∅⊆xs : ∀ {n} {xs : Subset n} → ∅ ⊆ xs
∅⊆xs {xs = []} p = p
∅⊆xs {xs = x ∷ xs} (there p) = there (∅⊆xs p)

x∈⁅y⁆→x≡y : ∀ {n} {x y : Fin n} → x ∈ ⁅ y ⁆ → x ≡ y
x∈⁅y⁆→x≡y {suc n} {zero} {zero} here = refl 
x∈⁅y⁆→x≡y {suc n} {suc i} {zero} (there p) with x∉∅ p
... | ()
x∈⁅y⁆→x≡y {y = suc y} (there p) = cong suc (x∈⁅y⁆→x≡y p)

∨-idem : Idempotent _≡_ _∨_
∨-idem true = refl
∨-idem false = refl

open IsCommutativeMonoid (CommutativeSemiring.+-isCommutativeMonoid commutativeSemiring-∨-∧)
  hiding (refl ; trans)
  renaming (sym to ∨-sym ; assoc to ∨-assoc ; comm to ∨-comm) 
  
∪-comm : ∀ {n} → Commutative {A = Subset n} _≡_ _∪_
∪-comm [] [] = refl
∪-comm (x ∷ xs) (y ∷ ys) = ∷-cong (∨-comm x y) (∪-comm xs ys) 

∪-assoc : ∀ {n} → Associative {A = Subset n} _≡_ _∪_ 
∪-assoc [] y z = refl
∪-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) = ∷-cong (∨-assoc x y z) (∪-assoc xs ys zs) 

∪-idem : ∀ {n} → Idempotent {A = Subset n} _≡_ _∪_
∪-idem [] = refl
∪-idem (x ∷ xs) = ∷-cong (∨-idem x) (∪-idem xs)

∪-cong : ∀ {n} {x₁ x₂ y₁ y₂ : Subset n} → x₁ ≡ x₂ → y₁ ≡ y₂ → x₁ ∪ y₁ ≡ x₂ ∪ y₂
∪-cong refl refl = refl

x∪∅≡x : ∀ {n} (x : Subset n) → x ∪ ∅ ≡ x
x∪∅≡x [] = refl
x∪∅≡x (true ∷ xs) = cong (_∷_ true) (x∪∅≡x xs)
x∪∅≡x (false ∷ xs) = cong (_∷_ false) (x∪∅≡x xs)

∅∪x≡x : ∀ {n} (x : Subset n) → ∅ ∪ x ≡ x
∅∪x≡x x = trans (∪-comm ∅ x) (x∪∅≡x x)

x⊆x∪y : ∀ {n} {x y : Subset n} → x ⊆ x ∪ y
x⊆x∪y {zero} {[]} ()
x⊆x∪y {suc n} {true ∷ xs} {y ∷ ys} {zero} here = here
x⊆x∪y {suc n} {false ∷ xs} {y ∷ ys} {zero} ()
x⊆x∪y {suc n} {true ∷ xs} {y ∷ ys} {suc i} (there xs[i]=x) = there (x⊆x∪y xs[i]=x)
x⊆x∪y {suc n} {false ∷ xs} {true ∷ ys} {suc i} (there xs[i]=x) = there (x⊆x∪y xs[i]=x)
x⊆x∪y {suc n} {false ∷ xs} {false ∷ ys} {suc i} (there xs[i]=x) = there (x⊆x∪y xs[i]=x) 

x∈xs→x∈xs∪ys : ∀ {n} {x : Fin n} {xs ys : Subset n} → x ∈ xs → x ∈ xs ∪ ys
x∈xs→x∈xs∪ys x∈xs = x⊆x∪y x∈xs

x∈ys→x∈xs∪ys : ∀ {n} {x : Fin n} {xs ys : Subset n} → x ∈ ys → x ∈ xs ∪ ys
x∈ys→x∈xs∪ys {x = x} {xs} x∈ys = subst (λ xs → x ∈ xs) (sym (∪-comm xs _)) (x⊆x∪y x∈ys) 

x∈xs-lookup : ∀ {n} {x} {xs : Subset n} → x ∈ xs → lookup x xs ≡ true
x∈xs-lookup here = refl
x∈xs-lookup (there xs[i]=x) = x∈xs-lookup xs[i]=x

x∈xs∪ys→x∈xs⊎x∈ys : ∀ {n} {x : Fin n} {xs ys : Subset n} → x ∈ xs ∪ ys → x ∈ xs ⊎ x ∈ ys
x∈xs∪ys→x∈xs⊎x∈ys {0} {x} {[]} {[]} x∈xs∪ys = inj₁ x∈xs∪ys
x∈xs∪ys→x∈xs⊎x∈ys {suc n} {zero} {true ∷ xs} {y ∷ ys} here = inj₁ here
x∈xs∪ys→x∈xs⊎x∈ys {suc n} {zero} {false ∷ xs} {true ∷ ys} here = inj₂ here
x∈xs∪ys→x∈xs⊎x∈ys {suc n} {zero} {false ∷ xs} {false ∷ ys} ()
x∈xs∪ys→x∈xs⊎x∈ys {suc n} {suc i} {x ∷ xs} {y ∷ ys} (there p) with x∈xs∪ys→x∈xs⊎x∈ys {xs = xs} p
... | inj₁ q = inj₁ (there q) 
... | inj₂ q = inj₂ (there q)

xs⊆zs→ys⊆zs→xs∪ys⊆zs : ∀ {n} {xs ys zs : Subset n} → xs ⊆ zs → ys ⊆ zs → xs ∪ ys ⊆ zs
xs⊆zs→ys⊆zs→xs∪ys⊆zs {xs = xs} xs→zs ys→zs x∈xs∪ys with (x∈xs∪ys→x∈xs⊎x∈ys {xs = xs} x∈xs∪ys)
... | inj₁ x∈xs = xs→zs x∈xs
... | inj₂ x∈ys = ys→zs x∈ys

⊆-trans : ∀ {n} {xs ys zs : Subset n} → xs ⊆ ys → ys ⊆ zs → xs ⊆ zs
⊆-trans xs⊆ys ys⊆zs = λ x → ys⊆zs (xs⊆ys x)

------------------------------------------------------------------------
-- More interesting properties

allInside : ∀ {n} (x : Fin n) → x ∈ all true
allInside zero    = here
allInside (suc x) = there (allInside x)

allOutside : ∀ {n} (x : Fin n) → x ∉ all false
allOutside zero    ()
allOutside (suc x) (there x∈) = allOutside x x∈

⊆⊇⟶≡ : ∀ {n} {p₁ p₂ : Subset n} →
       p₁ ⊆ p₂ → p₂ ⊆ p₁ → p₁ ≡ p₂
⊆⊇⟶≡ = helper _ _
  where
  helper : ∀ {n} (p₁ p₂ : Subset n) →
           p₁ ⊆ p₂ → p₂ ⊆ p₁ → p₁ ≡ p₂
  helper []            []             _   _   = refl
  helper (s₁ ∷ p₁)     (s₂ ∷ p₂)      ₁⊆₂ ₂⊆₁ with ⊆⊇⟶≡ (drop-∷-⊆ ₁⊆₂)
                                                        (drop-∷-⊆ ₂⊆₁)
  helper (false ∷ p) (false ∷ .p) ₁⊆₂ ₂⊆₁ | refl = refl
  helper (true  ∷ p) (true  ∷ .p) ₁⊆₂ ₂⊆₁ | refl = refl
  helper (false ∷ p) (true  ∷ .p) ₁⊆₂ ₂⊆₁ | refl with ₂⊆₁ here
  ...                                                | ()
  helper (true  ∷ p) (false ∷ .p) ₁⊆₂ ₂⊆₁ | refl with ₁⊆₂ here
  ...                                                | ()

∅⟶allOutside : ∀ {n} {p : Subset n} →
               Empty p → p ≡ all false
∅⟶allOutside {p = []}     ¬¬∅ = refl
∅⟶allOutside {p = s ∷ ps} ¬¬∅ with ∅⟶allOutside (drop-∷-Empty ¬¬∅)
∅⟶allOutside {p = false ∷ .(all false)} ¬¬∅ | refl = refl
∅⟶allOutside {p = true  ∷ .(all false)} ¬¬∅ | refl =
  ⊥-elim (¬¬∅ (zero , here))
