{-# OPTIONS --rewriting --confluence-check #-}

open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

variable
  A B : Set
  x y z : A
  xs ys zs : List A
  f : A → B
  m n : Nat

cong : (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

trans : x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

+zero : m + zero ≡ m
+zero {zero} = refl
+zero {suc m} = cong suc +zero

suc+zero : suc m + zero ≡ suc m
suc+zero = +zero

+suc : m + (suc n) ≡ suc (m + n)
+suc {zero} = refl
+suc {suc m} = cong suc +suc

zero+suc : zero + (suc n) ≡ suc n
zero+suc = refl

suc+suc : (suc m) + (suc n) ≡ suc (suc (m + n))
suc+suc = cong suc +suc

{-# REWRITE +zero +suc suc+zero zero+suc suc+suc #-}

map : (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = (f x) ∷ (map f xs)

_++_ : List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

++-[] : xs ++ [] ≡ xs
++-[] {xs = []} = refl
++-[] {xs = x ∷ xs} = cong (_∷_ x) ++-[]

∷-++-[] : (x ∷ xs) ++ [] ≡ x ∷ xs
∷-++-[] = ++-[]

map-id : map (λ x → x) xs ≡ xs
map-id {xs = []} = refl
map-id {xs = x ∷ xs} = cong (_∷_ x) map-id

map-id-∷ : map (λ x → x) (x ∷ xs) ≡ x ∷ xs
map-id-∷ = map-id

{-# REWRITE ++-[] ∷-++-[] #-}
{-# REWRITE map-id map-id-∷ #-}
