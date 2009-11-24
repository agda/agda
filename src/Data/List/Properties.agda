------------------------------------------------------------------------
-- List-related properties
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

-- Note that the lemmas below could be generalised to work with other
-- equalities than _≡_.

module Data.List.Properties where

open import Algebra
open import Data.List as List
private module LM {A} = Monoid (List.monoid A)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Bool
open import Data.Function
open import Data.Product as Prod hiding (map)
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
import Relation.Binary.EqReasoning as Eq

∷-injective : ∀ {a} {A : Set a} {x y xs ys} →
              (List A ∶ x ∷ xs) ≡ (y ∷ ys) → (x ≡ y) × (xs ≡ ys)
∷-injective refl = (refl , refl)

right-identity-unique : ∀ {a} {A : Set a} (xs : List A) {ys} →
                        xs ≡ xs ++ ys → ys ≡ []
right-identity-unique []       refl = refl
right-identity-unique (x ∷ xs) eq   =
  right-identity-unique xs (proj₂ (∷-injective eq))

left-identity-unique : ∀ {A : Set} {xs} (ys : List A) →
                       xs ≡ ys ++ xs → ys ≡ []
left-identity-unique               []       _  = refl
left-identity-unique {xs = []}     (y ∷ ys) ()
left-identity-unique {xs = x ∷ xs} (y ∷ ys) eq
  with left-identity-unique (ys ++ [ x ]) (begin
         xs                  ≡⟨ proj₂ (∷-injective eq) ⟩
         ys ++ x ∷ xs        ≡⟨ sym (LM.assoc ys [ x ] xs) ⟩
         (ys ++ [ x ]) ++ xs ∎)
  where open ≡-Reasoning
left-identity-unique {xs = x ∷ xs} (y ∷ []   ) eq | ()
left-identity-unique {xs = x ∷ xs} (y ∷ _ ∷ _) eq | ()

-- Map, sum, and append.

map-++-commute : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) xs ys →
                 map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-commute f []       ys = refl
map-++-commute f (x ∷ xs) ys =
  cong (_∷_ (f x)) (map-++-commute f xs ys)

sum-++-commute : ∀ xs ys → sum (xs ++ ys) ≡ sum xs + sum ys
sum-++-commute []       ys = refl
sum-++-commute (x ∷ xs) ys = begin
  x + sum (xs ++ ys)
                         ≡⟨ cong (_+_ x) (sum-++-commute xs ys) ⟩
  x + (sum xs + sum ys)
                         ≡⟨ sym $ +-assoc x _ _ ⟩
  (x + sum xs) + sum ys
                         ∎
  where
  open CommutativeSemiring commutativeSemiring hiding (_+_; sym)
  open ≡-Reasoning

-- Various properties about folds.

foldr-universal : ∀ {a b} {A : Set a} {B : Set b}
                  (h : List A → B) f e →
                  (h [] ≡ e) →
                  (∀ x xs → h (x ∷ xs) ≡ f x (h xs)) →
                  h ≗ foldr f e
foldr-universal h f e base step []       = base
foldr-universal h f e base step (x ∷ xs) = begin
  h (x ∷ xs)
    ≡⟨ step x xs ⟩
  f x (h xs)
    ≡⟨ cong (f x) (foldr-universal h f e base step xs) ⟩
  f x (foldr f e xs)
    ∎
  where open ≡-Reasoning

foldr-fusion : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
               (h : B → C) {f : A → B → B} {g : A → C → C} (e : B) →
               (∀ x y → h (f x y) ≡ g x (h y)) →
               h ∘ foldr f e ≗ foldr g (h e)
foldr-fusion h {f} {g} e fuse =
  foldr-universal (h ∘ foldr f e) g (h e) refl
                  (λ x xs → fuse x (foldr f e xs))

idIsFold : ∀ {a} {A : Set a} → id {A = List A} ≗ foldr _∷_ []
idIsFold = foldr-universal id _∷_ [] refl (λ _ _ → refl)

++IsFold : ∀ {a} {A : Set a} (xs ys : List A) →
           xs ++ ys ≡ foldr _∷_ ys xs
++IsFold xs ys =
  begin
    xs ++ ys
  ≡⟨ cong (λ xs → xs ++ ys) (idIsFold xs) ⟩
    foldr _∷_ [] xs ++ ys
  ≡⟨ foldr-fusion (λ xs → xs ++ ys) [] (λ _ _ → refl) xs ⟩
    foldr _∷_ ([] ++ ys) xs
  ≡⟨ refl ⟩
    foldr _∷_ ys xs
  ∎
  where open ≡-Reasoning

mapIsFold : ∀ {a b} {A : Set a} {B : Set b} {f : A → B} →
            map f ≗ foldr (λ x ys → f x ∷ ys) []
mapIsFold {f = f} =
  begin
    map f
  ≈⟨ cong (map f) ∘ idIsFold ⟩
    map f ∘ foldr _∷_ []
  ≈⟨ foldr-fusion (map f) [] (λ _ _ → refl) ⟩
    foldr (λ x ys → f x ∷ ys) []
  ∎
  where open Eq (_ →-setoid _)

concat-map : ∀ {a b} {A : Set a} {B : Set b} {f : A → B} →
             concat ∘ map (map f) ≗ map f ∘ concat
concat-map {b = b} {f = f} =
  begin
    concat ∘ map (map f)
  ≈⟨ cong concat ∘ mapIsFold {b = b} ⟩
    concat ∘ foldr (λ xs ys → map f xs ∷ ys) []
  ≈⟨ foldr-fusion {b = b} concat [] (λ _ _ → refl) ⟩
    foldr (λ ys zs → map f ys ++ zs) []
  ≈⟨ sym ∘
     foldr-fusion (map f) [] (λ ys zs → map-++-commute f ys zs) ⟩
    map f ∘ concat
  ∎
  where open Eq (_ →-setoid _)

map-id : ∀ {a} {A : Set a} → map id ≗ id {A = List A}
map-id = begin
  map id        ≈⟨ mapIsFold ⟩
  foldr _∷_ []  ≈⟨ sym ∘ idIsFold ⟩
  id            ∎
  where open Eq (_ →-setoid _)

map-compose : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
                {g : B → C} {f : A → B} →
              map (g ∘ f) ≗ map g ∘ map f
map-compose {g = g} {f} =
  begin
    map (g ∘ f)
  ≈⟨ cong (map (g ∘ f)) ∘ idIsFold ⟩
    map (g ∘ f) ∘ foldr _∷_ []
  ≈⟨ foldr-fusion (map (g ∘ f)) [] (λ _ _ → refl) ⟩
    foldr (λ a y → g (f a) ∷ y) []
  ≈⟨ sym ∘ foldr-fusion (map g) [] (λ _ _ → refl) ⟩
    map g ∘ foldr (λ a y → f a ∷ y) []
  ≈⟨ cong (map g) ∘ sym ∘ mapIsFold ⟩
    map g ∘ map f
  ∎
  where open Eq (_ →-setoid _)

foldr-cong : ∀ {a b} {A : Set a} {B : Set b}
               {f₁ f₂ : A → B → B} {e₁ e₂ : B} →
             (∀ x y → f₁ x y ≡ f₂ x y) → e₁ ≡ e₂ →
             foldr f₁ e₁ ≗ foldr f₂ e₂
foldr-cong {f₁ = f₁} {f₂} {e} f₁≗₂f₂ refl =
  begin
    foldr f₁ e
  ≈⟨ cong (foldr f₁ e) ∘ idIsFold ⟩
    foldr f₁ e ∘ foldr _∷_ []
  ≈⟨ foldr-fusion (foldr f₁ e) [] (λ x xs → f₁≗₂f₂ x (foldr f₁ e xs)) ⟩
    foldr f₂ e
  ∎
  where open Eq (_ →-setoid _)

map-cong : ∀ {a b} {A : Set a} {B : Set b} {f g : A → B} →
           f ≗ g → map f ≗ map g
map-cong {f = f} {g} f≗g =
  begin
    map f
  ≈⟨ mapIsFold ⟩
    foldr (λ x ys → f x ∷ ys) []
  ≈⟨ foldr-cong (λ x ys → cong₂ _∷_ (f≗g x) refl) refl ⟩
    foldr (λ x ys → g x ∷ ys) []
  ≈⟨ sym ∘ mapIsFold ⟩
    map g
  ∎
  where open Eq (_ →-setoid _)

-- Take, drop, and splitAt.

take++drop : ∀ {a} {A : Set a}
             n (xs : List A) → take n xs ++ drop n xs ≡ xs
take++drop zero    xs       = refl
take++drop (suc n) []       = refl
take++drop (suc n) (x ∷ xs) =
  cong (λ xs → x ∷ xs) (take++drop n xs)

splitAt-defn : ∀ {a} {A : Set a} n →
               splitAt {A = A} n ≗ < take n , drop n >
splitAt-defn zero    xs       = refl
splitAt-defn (suc n) []       = refl
splitAt-defn (suc n) (x ∷ xs) with splitAt n xs | splitAt-defn n xs
... | (ys , zs) | ih = cong (Prod.map (_∷_ x) id) ih

-- TakeWhile, dropWhile, and span.

takeWhile++dropWhile : ∀ {a} {A : Set a} (p : A → Bool) (xs : List A) →
                       takeWhile p xs ++ dropWhile p xs ≡ xs
takeWhile++dropWhile p []       = refl
takeWhile++dropWhile p (x ∷ xs) with p x
... | true  = cong (_∷_ x) (takeWhile++dropWhile p xs)
... | false = refl

span-defn : ∀ {a} {A : Set a} (p : A → Bool) →
            span p ≗ < takeWhile p , dropWhile p >
span-defn p []       = refl
span-defn p (x ∷ xs) with p x
... | true  = cong (Prod.map (_∷_ x) id) (span-defn p xs)
... | false = refl

-- Partition.

partition-defn : ∀ {a} {A : Set a} (p : A → Bool) →
                 partition p ≗ < filter p , filter (not ∘ p) >
partition-defn p []       = refl
partition-defn p (x ∷ xs)
 with p x | partition p xs | partition-defn p xs
...  | true  | (ys , zs) | eq = cong (Prod.map (_∷_ x) id) eq
...  | false | (ys , zs) | eq = cong (Prod.map id (_∷_ x)) eq

-- Inits, tails, and scanr.

scanr-defn : ∀ {a b} {A : Set a} {B : Set b}
             (f : A → B → B) (e : B) →
             scanr f e ≗ map (foldr f e) ∘ tails
scanr-defn f e []             = refl
scanr-defn f e (x ∷ [])       = refl
scanr-defn f e (x₁ ∷ x₂ ∷ xs)
  with scanr f e (x₂ ∷ xs) | scanr-defn f e (x₂ ∷ xs)
...  | [] | ()
...  | y ∷ ys | eq with ∷-injective eq
...        | y≡fx₂⦇f⦈xs , _ = cong₂ (λ z zs → f x₁ z ∷ zs) y≡fx₂⦇f⦈xs eq

scanl-defn : ∀ {a b} {A : Set a} {B : Set b}
             (f : A → B → A) (e : A) →
             scanl f e ≗ map (foldl f e) ∘ inits
scanl-defn f e []       = refl
scanl-defn f e (x ∷ xs) = cong (_∷_ e) (begin
     scanl f (f e x) xs
  ≡⟨ scanl-defn f (f e x) xs ⟩
     map (foldl f (f e x)) (inits xs)
  ≡⟨ refl ⟩
     map (foldl f e ∘ (_∷_ x)) (inits xs)
  ≡⟨ map-compose (inits xs) ⟩
     map (foldl f e) (map (_∷_ x) (inits xs))
  ∎)
  where open ≡-Reasoning

-- Length.

length-map : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) xs →
             length (map f xs) ≡ length xs
length-map f []       = refl
length-map f (x ∷ xs) = cong suc (length-map f xs)

length-++ : ∀ {a} {A : Set a} (xs : List A) {ys} →
            length (xs ++ ys) ≡ length xs + length ys
length-++ []       = refl
length-++ (x ∷ xs) = cong suc (length-++ xs)

length-gfilter : ∀ {a b} {A : Set a} {B : Set b} (p : A → Maybe B) xs →
                 length (gfilter p xs) ≤ length xs
length-gfilter p []       = z≤n
length-gfilter p (x ∷ xs) with p x
length-gfilter p (x ∷ xs) | just y  = s≤s (length-gfilter p xs)
length-gfilter p (x ∷ xs) | nothing = ≤-step (length-gfilter p xs)
