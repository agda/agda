------------------------------------------------------------------------
-- List-related properties
------------------------------------------------------------------------

module Data.List.Properties where

open import Data.List
open import Data.Nat
open import Data.Nat.Properties
open import Data.Function
open import Logic
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Algebra

map-++-commute :  forall {a b} (f : a -> b) xs ys
               -> map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-commute f []       ys = ≡-refl
map-++-commute f (x ∷ xs) ys =
  ≡-cong (_∷_ (f x)) (map-++-commute f xs ys)

sum-++-commute : forall xs ys -> sum (xs ++ ys) ≡ sum xs + sum ys
sum-++-commute []       ys = ≡-refl
sum-++-commute (x ∷ xs) ys = begin
  x + sum (xs ++ ys)
                         ≡⟨ ≡-cong (_+_ x) (sum-++-commute xs ys) ⟩
  x + (sum xs + sum ys)
                         ≡⟨ sym $ +-assoc x _ _ ⟩
  (x + sum xs) + sum ys
                         ∎
  where open CommutativeSemiring ℕ-commutativeSemiring hiding (_+_)

foldr-universal : forall {a b} -> (h : [ a ] -> b) -> forall f e ->
  (h [] ≡ e) -> (forall x xs -> h (x ∷ xs) ≡ f x (h xs)) ->
  (forall x -> h x ≡ foldr f e x)
foldr-universal h f e base step []       = base
foldr-universal h f e base step (x ∷ xs) =
  ≡-trans (step x xs)
          (≡-cong (f x) (foldr-universal h f e base step xs))

foldr-fusion : forall {a b c} -> (h : b -> c) -> {f : a -> b -> b} -> 
   {g : a -> c -> c} -> {e : b} -> 
   (push : forall x y -> h (f x y) ≡ g x (h y)) ->
       forall xs -> (h ∘ foldr f e) xs ≡ foldr g (h e) xs
foldr-fusion h {f} {g} {e} fuse =
  foldr-universal (h ∘ foldr f e) g (h e) ≡-refl
              (\x xs -> fuse x (foldr f e xs))

idIsFold : forall {a} -> (xs : [ a ]) ->
              (id xs ≡ foldr _∷_ [] xs)
idIsFold = foldr-universal id _∷_ [] ≡-refl (\_ _ -> ≡-refl)

++IsFold : forall {a} -> (xs : [ a ]) -> {ys : [ a ]} -> 
             xs ++ ys ≡ (foldr _∷_ ys xs)
++IsFold xs {ys} = 
     begin
          xs ++ ys
     ≡⟨ ≡-cong (\xs -> xs ++ ys) (idIsFold xs) ⟩ 
          (foldr _∷_ [] xs) ++ ys
     ≡⟨ foldr-fusion (\xs -> xs ++ ys) (\_ _ -> ≡-refl) xs ⟩
          foldr _∷_ ([] ++ ys) xs
     ≡⟨ ≡-refl ⟩ 
          foldr _∷_ ys xs 
     ∎

private

  infix 4 _≐_

  _≐_ : {a b : Set} -> (a -> b) -> (a -> b) -> Set
  f ≐ g = forall x -> f x ≡ g x

mapIsFold : forall {a b} -> {f : a -> b} ->
              map f ≐ foldr (\x ys -> f x ∷ ys) []
mapIsFold {_} {_} {f} xs =
     begin
       map f xs
     ≡⟨ ≡-cong (map f) (idIsFold xs) ⟩ 
       (map f ∘ foldr _∷_ []) xs
     ≡⟨ foldr-fusion (map f) (\_ _ -> ≡-refl) xs ⟩ 
       foldr (\x ys -> f x ∷ ys) [] xs
     ∎

concat-map : forall {a b} -> {f : a -> b} -> 
          concat ∘ map (map f) ≐ map f ∘ concat
concat-map {A} {B} {f} xs = 
     begin
       (concat ∘ map (map f)) xs
     ≡⟨ ≡-cong concat (mapIsFold xs) ⟩ 
       (concat ∘ foldr (\xs ys -> map f xs ∷ ys) []) xs
     ≡⟨ foldr-fusion concat (\_ _ -> ≡-refl) xs ⟩ 
       foldr (\ys zs -> map f ys ++ zs) [] xs
     ≡⟨ ≡-sym (foldr-fusion (map f) (\ys zs -> map-++-commute f ys zs) xs) ⟩ 
       (map f ∘ concat) xs
     ∎

map-compose : forall {a b c} -> {g : b -> c} -> {f : a -> b} -> 
                 map (g ∘ f) ≐ map g ∘ map f
map-compose {_} {_} {_} {g} {f} xs = 
     begin
       map (g ∘ f) xs
     ≡⟨ ≡-cong (map (g ∘ f)) (idIsFold xs) ⟩ 
       (map (g ∘ f) ∘ foldr _∷_ []) xs
     ≡⟨ foldr-fusion (map (g ∘ f)) (\_ _ -> ≡-refl) xs ⟩ 
       foldr (\a y -> g (f a) ∷ y) [] xs
     ≡⟨ ≡-sym (foldr-fusion (map g) (\_ _ -> ≡-refl) xs) ⟩ 
       (map g ∘ foldr (\a y -> f a ∷ y) []) xs
     ≡⟨ ≡-cong (map g) (≡-sym (mapIsFold xs))  ⟩ 
       (map g ∘ map f) xs
     ∎

foldr-eq : forall {a b} -> {f g : a -> b -> b} -> {e : b} ->
             (forall x -> forall y -> f x y ≡ g x y) ->
               foldr f e ≐ foldr g e
foldr-eq {A} {B} {f} {g} {e} f≡g xs =
     begin
       foldr f e xs
     ≡⟨ ≡-cong (foldr f e) (idIsFold xs) ⟩ 
       (foldr f e ∘ foldr _∷_ []) xs
     ≡⟨ foldr-fusion (foldr f e) (\x ys -> f≡g x (foldr f e ys)) xs ⟩ 
       foldr g e xs
     ∎

map-eq : forall {a b} -> {f g : a -> b} ->
            f ≐ g -> map f ≐ map g
map-eq {_} {_} {f} {g} f≡g xs = 
     begin
       map f xs
     ≡⟨ mapIsFold xs ⟩ 
       foldr (\x ys -> f x ∷ ys) [] xs
     ≡⟨ foldr-eq (\x ys -> ≡-cong (\y -> y ∷ ys) (f≡g x)) xs ⟩
       foldr (\x ys -> g x ∷ ys) [] xs
     ≡⟨ ≡-sym (mapIsFold xs) ⟩ 
       map g xs
     ∎
