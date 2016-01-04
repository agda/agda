\AgdaHide{
\begin{code}
module Issue854.Context where

open import Level hiding (zero; suc)
open import Data.Nat hiding (_⊔_)
open import Data.Fin
open import Relation.Binary hiding (Rel)

infix  4 _∋_
infixl 5 _▻_

------------------------------------------------------------------------

data Snoc {a} (A : Set a) : Set a where
  []  : Snoc A
  _▻_ : (xs : Snoc A) (x : A) → Snoc A

data _∋_ {a} {A : Set a} : Snoc A → A → Set a where
  zero : ∀ {x xs} → xs ▻ x ∋ x
  suc  : ∀ {x y xs} → xs ∋ x → xs ▻ y ∋ x

length : ∀ {a} {A : Set a} → Snoc A → ℕ
length []       = 0
length (xs ▻ _) = suc (length xs)

index : ∀ {a} {A : Set a} {xs : Snoc A} {x : A} → xs ∋ x → Fin (length xs)
index zero    = zero
index (suc p) = suc (index p)

data Rel {a b ℓ} {A : Set a} {B : Set b}
         (_∼_ : REL A B ℓ) : Snoc A → Snoc B → Set (a ⊔ b ⊔ ℓ) where
  []  : Rel _∼_ [] []
  _▻_ : ∀ {x xs y ys} → x ∼ y → Rel _∼_ xs ys → Rel _∼_ (xs ▻ x) (ys ▻ y)
\end{code}
}
