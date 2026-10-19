
open import Common.List
open import Common.Equality

map-append : ∀{A B : Set}(f : A → B) (xs {ys} : List A) →
             map f (xs ++ ys) ≡ map f xs ++ map f ys
map-append f [] = refl
map-append f (x ∷ xs) = {!cong (f x ∷_)!}   -- Keep section on C-c C-r

map-append₂ : ∀{A B : Set}(f : A → B) (xs {ys} : List A) →
             map f (xs ++ ys) ≡ map f xs ++ map f ys
map-append₂ f [] = refl
map-append₂ f (x ∷ xs) = {!cong (λ section → f x ∷ section)!} -- Keep lambda on C-c C-r

-- Check that we print sections in goals
postulate
  _+_ : Set → Set → Set
  μ : (Set → Set) → Set

foo : (A : Set) → μ (_+ A)
foo A = {!!}

bar : (A : Set) → μ (λ section → section + A)
bar A = {!!}
