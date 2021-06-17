open import Agda.Primitive
open import Agda.Builtin.List
open import Agda.Builtin.Equality

private
  variable
    a p : Level
    A : Set a
    P Q : A → Set p

data Any {a p} {A : Set a} (P : A → Set p) : List A → Set (a ⊔ p) where
  here  : ∀ {x xs} (px  : P x)      → Any P (x ∷ xs)
  there : ∀ {x xs} (pxs : Any P xs) → Any P (x ∷ xs)

map : (∀ {x} → P x → Q x) → (∀ {xs} → Any P xs → Any Q xs)
map g (here px)   = here (g px)
map g (there pxs) = there (map g pxs)

postulate
  map-id : ∀ (f : ∀ {x} → P x → P x) → (∀ {x} (p : P x) → f p ≡ p) →
          ∀ {xs} → (p : Any P xs) → map f p ≡ p
