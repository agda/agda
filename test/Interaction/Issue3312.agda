-- open import Data.List
-- open import Data.Fin

open import Agda.Builtin.Nat public
  using (Nat; zero; suc)

open import Agda.Builtin.List public
  using (List; []; _∷_)

data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (suc n)
  fsuc  : {n : Nat} (i : Fin n) → Fin (suc n)

foldr : ∀ {a b} {A : Set a} {B : Set b} → (A → B → B) → B → List A → B
foldr c n []       = n
foldr c n (x ∷ xs) = c x (foldr c n xs)

length : ∀ {a} {A : Set a} → List A → Nat
length = foldr (λ _ → suc) 0

lookup : ∀ {a} {A : Set a} (xs : List A) → Fin (length xs) → A
lookup [] ()
lookup (x ∷ xs) fzero = x
lookup (x ∷ xs) (fsuc i) = lookup xs i

data ListD {I : Set} (T : I → Set) : List I → Set where
  nilD  : ListD T []
  consD : ∀ {x xs} → (elem : T x) → (rest : ListD T xs) → ListD T (x ∷ xs)

lookupD : {I : Set} {T : I → Set} {xs : List I} → ListD T xs → (at : Fin (length xs)) → {!lookup ? ?!}
lookupD xs at = {!!}
