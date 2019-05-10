{-# OPTIONS --rewriting --confluence-check #-}

module NewEquations where

open import Common.Prelude hiding (map; _++_)
open import Common.Equality

infixr 5 _++_

map : ∀ {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = (f x) ∷ (map f xs)

_++_ : ∀ {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

fold : ∀ {A B : Set} → (A → B → B) → B → List A → B
fold f v [] = v
fold f v (x ∷ xs) = f x (fold f v xs)

++-[] : ∀ {A} {xs : List A} → xs ++ [] ≡ xs
++-[] {xs = []} = refl
++-[] {xs = x ∷ xs} = cong (_∷_ x) ++-[]

++-assoc : ∀ {A} {xs ys zs : List A} → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc {xs = []} = refl
++-assoc {xs = x ∷ xs} = cong (_∷_ x) (++-assoc {xs = xs})

map-id : ∀ {A} {xs : List A} → map (λ x → x) xs ≡ xs
map-id {xs = []} = refl
map-id {xs = x ∷ xs} = cong (_∷_ x) map-id

map-fuse : ∀ {A B C} {f : B → C} {g : A → B} {xs : List A} → map f (map g xs) ≡ map (λ x → f (g x)) xs
map-fuse {xs = []} = refl
map-fuse {xs = x ∷ xs} = cong (_∷_ _) map-fuse

map-++ : ∀ {A B} {f : A → B} {xs ys : List A} → map f (xs ++ ys) ≡ (map f xs) ++ (map f ys)
map-++ {xs = []} = refl
map-++ {xs = x ∷ xs} = cong (_∷_ _) (map-++ {xs = xs})

fold-map : ∀ {A B C} {f : A → B} {c : B → C → C} {n : C} {xs : List A} →
           fold c n (map f xs) ≡ fold (λ x → c (f x)) n xs
fold-map {xs = []} = refl
fold-map {c = c} {xs = x ∷ xs} = cong (c _) (fold-map {xs = xs})

fold-++ : ∀ {A B} {c : A → B → B} {n : B} {xs ys : List A} →
          fold c n (xs ++ ys) ≡ fold c (fold c n ys) xs
fold-++ {xs = []} = refl
fold-++ {c = c} {xs = x ∷ xs} = cong (c _) (fold-++ {xs = xs})

{-# BUILTIN REWRITE _≡_ #-}
{-# REWRITE ++-[] #-}
{-# REWRITE ++-assoc #-}
{-# REWRITE map-id #-}
{-# REWRITE map-fuse #-}
{-# REWRITE map-++ #-}
{-# REWRITE fold-++ #-}
{-# REWRITE fold-map #-} -- Note: confluence check fails if we add fold-map before fold-++

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

swap : ∀ {A B} → A × B → B × A
swap (x , y) = y , x

test₁ : ∀ {A B} {xs : List (A × B)} → map swap (map swap xs) ≡ xs
test₁ = refl
