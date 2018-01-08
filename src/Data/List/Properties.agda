------------------------------------------------------------------------
-- The Agda standard library
--
-- List-related properties
------------------------------------------------------------------------

-- Note that the lemmas below could be generalised to work with other
-- equalities than _≡_.

module Data.List.Properties where

open import Algebra
open import Algebra.FunctionProperties
import Algebra.Monoid-solver
open import Category.Monad
open import Data.Bool.Base using (Bool; false; true; not; if_then_else_)
open import Data.List as List
open import Data.List.All using (All; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product as Prod hiding (map)
open import Function
import Relation.Binary.EqReasoning as EqR
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≢_; _≗_; refl)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Unary using (Decidable; ∁; ∁?)

private
  open module LMP {ℓ} = RawMonadPlus (List.monadPlus {ℓ = ℓ})
  module LM {a} {A : Set a} = Monoid (List.monoid A)

module List-solver {a} {A : Set a} =
  Algebra.Monoid-solver (monoid A) renaming (id to nil)

------------------------------------------------------------------------
-- _∷_

module _ {a} {A : Set a} {x y : A} {xs ys : List A} where

 ∷-injective : x ∷ xs ≡ y List.∷ ys → x ≡ y × xs ≡ ys
 ∷-injective refl = (refl , refl)

 ∷-injectiveˡ : x ∷ xs ≡ y List.∷ ys → x ≡ y
 ∷-injectiveˡ refl = refl

 ∷-injectiveʳ : x ∷ xs ≡ y List.∷ ys → xs ≡ ys
 ∷-injectiveʳ refl = refl

------------------------------------------------------------------------
-- map

module _ {a} {A : Set a} where

  map-id : map id ≗ id {A = List A}
  map-id []       = refl
  map-id (x ∷ xs) = P.cong (x ∷_) (map-id xs)

  map-id₂ : ∀ {f : A → A} {xs} → All (λ x → f x ≡ x) xs → map f xs ≡ xs
  map-id₂ []         = refl
  map-id₂ (fx≡x ∷ pxs) = P.cong₂ _∷_ fx≡x (map-id₂ pxs)

module _ {a b} {A : Set a} {B : Set b} where

  map-++-commute : ∀ (f : A → B) xs ys →
                   map f (xs ++ ys) ≡ map f xs ++ map f ys
  map-++-commute f []       ys = refl
  map-++-commute f (x ∷ xs) ys = P.cong (f x ∷_) (map-++-commute f xs ys)

  map-cong : ∀ {f g : A → B} → f ≗ g → map f ≗ map g
  map-cong f≗g []       = refl
  map-cong f≗g (x ∷ xs) = P.cong₂ _∷_ (f≗g x) (map-cong f≗g xs)

  map-cong₂ : ∀ {f g : A → B} {xs} →
              All (λ x → f x ≡ g x) xs → map f xs ≡ map g xs
  map-cong₂ []                = refl
  map-cong₂ (fx≡gx ∷ fxs≡gxs) = P.cong₂ _∷_ fx≡gx (map-cong₂ fxs≡gxs)

  length-map : ∀ (f : A → B) xs → length (map f xs) ≡ length xs
  length-map f []       = refl
  length-map f (x ∷ xs) = P.cong suc (length-map f xs)

module _ {a b c} {A : Set a} {B : Set b} {C : Set c} where

  map-compose : {g : B → C} {f : A → B} → map (g ∘ f) ≗ map g ∘ map f
  map-compose [] = refl
  map-compose (x ∷ xs) = P.cong (_ ∷_) (map-compose xs)

------------------------------------------------------------------------
-- mapMaybe

module _ {a} {A : Set a} where

  mapMaybe-just : (xs : List A) → mapMaybe just xs ≡ xs
  mapMaybe-just []       = refl
  mapMaybe-just (x ∷ xs) = P.cong (x ∷_) (mapMaybe-just xs)

  mapMaybe-nothing : (xs : List A) →
                     mapMaybe {B = A} (λ _ → nothing) xs ≡ []
  mapMaybe-nothing []       = refl
  mapMaybe-nothing (x ∷ xs) = mapMaybe-nothing xs

module _ {a b} {A : Set a} {B : Set b} (f : A → Maybe B) where

  mapMaybe-concatMap : mapMaybe f ≗ concatMap (fromMaybe ∘ f)
  mapMaybe-concatMap [] = refl
  mapMaybe-concatMap (x ∷ xs) with f x
  ... | just y  = P.cong (y ∷_) (mapMaybe-concatMap xs)
  ... | nothing = mapMaybe-concatMap xs

  length-mapMaybe : ∀ xs → length (mapMaybe f xs) ≤ length xs
  length-mapMaybe []       = z≤n
  length-mapMaybe (x ∷ xs) with f x
  ... | just y  = s≤s (length-mapMaybe xs)
  ... | nothing = ≤-step (length-mapMaybe xs)

------------------------------------------------------------------------
-- _++_

module _ {a} {A : Set a} where

  ++-identityˡ : LeftIdentity (_≡_ {A = List A}) [] _++_
  ++-identityˡ xs = refl

  ++-identityʳ : RightIdentity (_≡_ {A = List A}) [] _++_
  ++-identityʳ []       = refl
  ++-identityʳ (x ∷ xs) = P.cong (x ∷_) (++-identityʳ xs)

  ++-identity : Identity (_≡_ {A = List A}) [] _++_
  ++-identity = ++-identityˡ , ++-identityʳ

  ++-identityʳ-unique : ∀ (xs : List A) {ys} → xs ≡ xs ++ ys → ys ≡ []
  ++-identityʳ-unique []       refl = refl
  ++-identityʳ-unique (x ∷ xs) eq   =
    ++-identityʳ-unique xs (proj₂ (∷-injective eq))

  ++-identityˡ-unique : ∀ {xs} (ys : List A) → xs ≡ ys ++ xs → ys ≡ []
  ++-identityˡ-unique               []       _  = refl
  ++-identityˡ-unique {xs = []}     (y ∷ ys) ()
  ++-identityˡ-unique {xs = x ∷ xs} (y ∷ ys) eq
    with ++-identityˡ-unique (ys ++ [ x ]) (begin
         xs                  ≡⟨ proj₂ (∷-injective eq) ⟩
         ys ++ x ∷ xs        ≡⟨ P.sym (LM.assoc ys [ x ] xs) ⟩
         (ys ++ [ x ]) ++ xs ∎)
    where open P.≡-Reasoning
  ++-identityˡ-unique {xs = x ∷ xs} (y ∷ []   ) eq | ()
  ++-identityˡ-unique {xs = x ∷ xs} (y ∷ _ ∷ _) eq | ()

  length-++ : ∀ (xs : List A) {ys} → length (xs ++ ys) ≡ length xs + length ys
  length-++ []       = refl
  length-++ (x ∷ xs) = P.cong suc (length-++ xs)

------------------------------------------------------------------------
-- foldr

foldr-universal : ∀ {a b} {A : Set a} {B : Set b}
                  (h : List A → B) f e → (h [] ≡ e) →
                  (∀ x xs → h (x ∷ xs) ≡ f x (h xs)) →
                  h ≗ foldr f e
foldr-universal h f e base step []       = base
foldr-universal h f e base step (x ∷ xs) = begin
    h (x ∷ xs)
  ≡⟨ step x xs ⟩
    f x (h xs)
  ≡⟨ P.cong (f x) (foldr-universal h f e base step xs) ⟩
    f x (foldr f e xs)
  ∎
  where open P.≡-Reasoning

foldr-cong : ∀ {a b} {A : Set a} {B : Set b}
             {f g : A → B → B} {d e : B} →
             (∀ x y → f x y ≡ g x y) → d ≡ e →
             foldr f d ≗ foldr g e
foldr-cong f≗g refl []      = refl
foldr-cong f≗g d≡e (x ∷ xs) rewrite foldr-cong f≗g d≡e xs = f≗g x _

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
  ≡⟨ P.cong (_++ ys) (idIsFold xs) ⟩
    foldr _∷_ [] xs ++ ys
  ≡⟨ foldr-fusion (_++ ys) [] (λ _ _ → refl) xs ⟩
    foldr _∷_ ([] ++ ys) xs
  ≡⟨⟩
    foldr _∷_ ys xs
  ∎
  where open P.≡-Reasoning

foldr-++ : ∀ {a b} {A : Set a} {B : Set b} (f : A → B → B) x ys zs →
           foldr f x (ys ++ zs) ≡ foldr f (foldr f x zs) ys
foldr-++ f x []       zs = refl
foldr-++ f x (y ∷ ys) zs = P.cong (f y) (foldr-++ f x ys zs)

mapIsFold : ∀ {a b} {A : Set a} {B : Set b} {f : A → B} →
            map f ≗ foldr (λ x ys → f x ∷ ys) []
mapIsFold {f = f} =
  begin
    map f
  ≈⟨ P.cong (map f) ∘ idIsFold ⟩
    map f ∘ foldr _∷_ []
  ≈⟨ foldr-fusion (map f) [] (λ _ _ → refl) ⟩
    foldr (λ x ys → f x ∷ ys) []
  ∎
  where open EqR (P._→-setoid_ _ _)

foldr-∷ʳ : ∀ {a b} {A : Set a} {B : Set b} (f : A → B → B) x y ys →
           foldr f x (ys ∷ʳ y) ≡ foldr f (f y x) ys
foldr-∷ʳ f x y []       = refl
foldr-∷ʳ f x y (z ∷ ys) = P.cong (f z) (foldr-∷ʳ f x y ys)

------------------------------------------------------------------------
-- foldl

module _ {a b} {A : Set a} {B : Set b} where

  foldl-++ : ∀ (f : A → B → A) x ys zs →
             foldl f x (ys ++ zs) ≡ foldl f (foldl f x ys) zs
  foldl-++ f x []       zs = refl
  foldl-++ f x (y ∷ ys) zs = foldl-++ f (f x y) ys zs

  foldl-∷ʳ : ∀ (f : A → B → A) x y ys →
             foldl f x (ys ∷ʳ y) ≡ f (foldl f x ys) y
  foldl-∷ʳ f x y []       = refl
  foldl-∷ʳ f x y (z ∷ ys) = foldl-∷ʳ f (f x z) y ys

------------------------------------------------------------------------
-- concat

module _ {a b} {A : Set a} {B : Set b} where

  concat-map : ∀ {f : A → B} → concat ∘ map (map f) ≗ map f ∘ concat
  concat-map {f = f} =
    begin
      concat ∘ map (map f)
    ≈⟨ P.cong concat ∘ mapIsFold ⟩
      concat ∘ foldr (λ xs → map f xs ∷_) []
    ≈⟨ foldr-fusion concat [] (λ _ _ → refl) ⟩
      foldr (λ ys → map f ys ++_) []
    ≈⟨ P.sym ∘ foldr-fusion (map f) [] (map-++-commute f) ⟩
      map f ∘ concat
    ∎
    where open EqR (P._→-setoid_ _ _)

------------------------------------------------------------------------
-- sum

sum-++-commute : ∀ xs ys → sum (xs ++ ys) ≡ sum xs + sum ys
sum-++-commute []       ys = refl
sum-++-commute (x ∷ xs) ys = begin
  x + sum (xs ++ ys)     ≡⟨ P.cong (x +_) (sum-++-commute xs ys) ⟩
  x + (sum xs + sum ys)  ≡⟨ P.sym (+-assoc x _ _) ⟩
  (x + sum xs) + sum ys  ∎
  where open P.≡-Reasoning

------------------------------------------------------------------------
-- replicate

module _ {a} {A : Set a} where

  length-replicate : ∀ n {x : A} → length (replicate n x) ≡ n
  length-replicate zero    = refl
  length-replicate (suc n) = P.cong suc (length-replicate n)

------------------------------------------------------------------------
-- scanr

module _ {a b} {A : Set a} {B : Set b} where

  scanr-defn : ∀ (f : A → B → B) (e : B) →
               scanr f e ≗ map (foldr f e) ∘ tails
  scanr-defn f e []             = refl
  scanr-defn f e (x ∷ [])       = refl
  scanr-defn f e (x ∷ y ∷ xs)
    with scanr f e (y ∷ xs) | scanr-defn f e (y ∷ xs)
  ... | []     | ()
  ... | z ∷ zs | eq with ∷-injective eq
  ...   | z≡fy⦇f⦈xs , _ = P.cong₂ (λ z → f x z ∷_) z≡fy⦇f⦈xs eq

------------------------------------------------------------------------
-- scanl

module _ {a b} {A : Set a} {B : Set b} where

  scanl-defn : ∀ (f : A → B → A) (e : A) →
               scanl f e ≗ map (foldl f e) ∘ inits
  scanl-defn f e []       = refl
  scanl-defn f e (x ∷ xs) = P.cong (e ∷_) (begin
     scanl f (f e x) xs
   ≡⟨ scanl-defn f (f e x) xs ⟩
     map (foldl f (f e x)) (inits xs)
   ≡⟨ refl ⟩
     map (foldl f e ∘ (x ∷_)) (inits xs)
   ≡⟨ map-compose (inits xs) ⟩
     map (foldl f e) (map (x ∷_) (inits xs))
   ∎)
   where open P.≡-Reasoning

------------------------------------------------------------------------
-- take, drop, splitAt

module _ {a} {A : Set a} where

  take++drop : ∀ n (xs : List A) → take n xs ++ drop n xs ≡ xs
  take++drop zero    xs       = refl
  take++drop (suc n) []       = refl
  take++drop (suc n) (x ∷ xs) = P.cong (x ∷_) (take++drop n xs)

  splitAt-defn : ∀ n → splitAt {A = A} n ≗ < take n , drop n >
  splitAt-defn zero    xs       = refl
  splitAt-defn (suc n) []       = refl
  splitAt-defn (suc n) (x ∷ xs) with splitAt n xs | splitAt-defn n xs
  ... | (ys , zs) | ih = P.cong (Prod.map (x ∷_) id) ih

------------------------------------------------------------------------
-- takeWhile, dropWhile, and span

module _ {a} {A : Set a} (p : A → Bool) where

  takeWhile++dropWhile : ∀ xs → takeWhile p xs ++ dropWhile p xs ≡ xs
  takeWhile++dropWhile []       = refl
  takeWhile++dropWhile (x ∷ xs) with p x
  ... | true  = P.cong (x ∷_) (takeWhile++dropWhile xs)
  ... | false = refl

  span-defn : span p ≗ < takeWhile p , dropWhile p >
  span-defn []       = refl
  span-defn (x ∷ xs) with p x
  ... | true  = P.cong (Prod.map (x ∷_) id) (span-defn xs)
  ... | false = refl

------------------------------------------------------------------------
-- filter

module _ {a p} {A : Set a} {P : A → Set p} (P? : Decidable P) where

  filter-all : ∀ {xs} → All P xs → filter P? xs ≡ xs
  filter-all {[]}     []         = refl
  filter-all {x ∷ xs} (px ∷ pxs) with P? x
  ... | no  ¬px = contradiction px ¬px
  ... | yes _   = P.cong (x ∷_) (filter-all pxs)

  filter-none : ∀ {xs} → All (∁ P) xs → filter P? xs ≡ []
  filter-none {[]}     []           = refl
  filter-none {x ∷ xs} (¬px ∷ ¬pxs) with P? x
  ... | no  _  = filter-none ¬pxs
  ... | yes px = contradiction px ¬px

  length-filter : ∀ xs → length (filter P? xs) ≤ length xs
  length-filter []       = z≤n
  length-filter (x ∷ xs) with P? x
  ... | no  _ = ≤-step (length-filter xs)
  ... | yes _ = s≤s (length-filter xs)

------------------------------------------------------------------------
-- partition

module _ {a p} {A : Set a} {P : A → Set p} (P? : Decidable P) where

  partition-defn : partition P? ≗ < filter P? , filter (∁? P?) >
  partition-defn []       = refl
  partition-defn (x ∷ xs) with P? x
  ...  | yes Px = P.cong (Prod.map (x ∷_) id) (partition-defn xs)
  ...  | no ¬Px = P.cong (Prod.map id (x ∷_)) (partition-defn xs)

------------------------------------------------------------------------
-- reverse

module _ {a} {A : Set a} where

  unfold-reverse : ∀ (x : A) xs → reverse (x ∷ xs) ≡ reverse xs ∷ʳ x
  unfold-reverse x xs = helper [ x ] xs
    where
    open P.≡-Reasoning
    helper : (xs ys : List A) → foldl (flip _∷_) xs ys ≡ reverse ys ++ xs
    helper xs []       = refl
    helper xs (y ∷ ys) = begin
      foldl (flip _∷_) (y ∷ xs) ys  ≡⟨ helper (y ∷ xs) ys ⟩
      reverse ys ++ y ∷ xs          ≡⟨ P.sym $ LM.assoc (reverse ys) _ _ ⟩
      (reverse ys ∷ʳ y) ++ xs       ≡⟨ P.sym $ P.cong (_++ xs) (unfold-reverse y ys) ⟩
      reverse (y ∷ ys) ++ xs        ∎

  reverse-++-commute : (xs ys : List A) →
                       reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
  reverse-++-commute []       ys = P.sym (proj₂ LM.identity _)
  reverse-++-commute (x ∷ xs) ys = begin
    reverse (x ∷ xs ++ ys)               ≡⟨ unfold-reverse x (xs ++ ys) ⟩
    reverse (xs ++ ys) ++ [ x ]          ≡⟨ P.cong (_++ [ x ]) (reverse-++-commute xs ys) ⟩
    (reverse ys ++ reverse xs) ++ [ x ]  ≡⟨ LM.assoc (reverse ys) _ _ ⟩
    reverse ys ++ (reverse xs ++ [ x ])  ≡⟨ P.sym $ P.cong (reverse ys ++_) (unfold-reverse x xs) ⟩
    reverse ys ++ reverse (x ∷ xs)       ∎
    where open P.≡-Reasoning

  reverse-involutive : Involutive _≡_ (reverse {A = A})
  reverse-involutive [] = refl
  reverse-involutive (x ∷ xs) = begin
    reverse (reverse (x ∷ xs))   ≡⟨ P.cong reverse $ unfold-reverse x xs ⟩
    reverse (reverse xs ∷ʳ x)    ≡⟨ reverse-++-commute (reverse xs) ([ x ]) ⟩
    x ∷ reverse (reverse (xs))   ≡⟨ P.cong (x ∷_) $ reverse-involutive xs ⟩
    x ∷ xs                       ∎
    where open P.≡-Reasoning

  length-reverse : (xs : List A) → length (reverse xs) ≡ length xs
  length-reverse []       = refl
  length-reverse (x ∷ xs) = begin
    length (reverse (x ∷ xs))   ≡⟨ P.cong length $ unfold-reverse x xs ⟩
    length (reverse xs ∷ʳ x)    ≡⟨ length-++ (reverse xs) ⟩
    length (reverse xs) + 1     ≡⟨ P.cong (_+ 1) (length-reverse xs) ⟩
    length xs + 1               ≡⟨ +-comm _ 1 ⟩
    suc (length xs)             ∎
    where open P.≡-Reasoning

module _ {a b} {A : Set a} {B : Set b} where

  reverse-map-commute : (f : A → B) (xs : List A) →
                        map f (reverse xs) ≡ reverse (map f xs)
  reverse-map-commute f []       = refl
  reverse-map-commute f (x ∷ xs) = begin
    map f (reverse (x ∷ xs))   ≡⟨ P.cong (map f) $ unfold-reverse x xs ⟩
    map f (reverse xs ∷ʳ x)    ≡⟨ map-++-commute f (reverse xs) ([ x ]) ⟩
    map f (reverse xs) ∷ʳ f x  ≡⟨ P.cong (_∷ʳ f x) $ reverse-map-commute f xs ⟩
    reverse (map f xs) ∷ʳ f x  ≡⟨ P.sym $ unfold-reverse (f x) (map f xs) ⟩
    reverse (map f (x ∷ xs))   ∎
    where open P.≡-Reasoning

  reverse-foldr : ∀ (f : A → B → B) x ys →
                  foldr f x (reverse ys) ≡ foldl (flip f) x ys
  reverse-foldr f x []       = refl
  reverse-foldr f x (y ∷ ys) = begin
    foldr f x (reverse (y ∷ ys)) ≡⟨ P.cong (foldr f x) (unfold-reverse y ys) ⟩
    foldr f x ((reverse ys) ∷ʳ y) ≡⟨ foldr-∷ʳ f x y (reverse ys) ⟩
    foldr f (f y x) (reverse ys)  ≡⟨ reverse-foldr f (f y x) ys ⟩
    foldl (flip f) (f y x) ys     ∎
    where open P.≡-Reasoning

  reverse-foldl : ∀ (f : A → B → A) x ys →
                  foldl f x (reverse ys) ≡ foldr (flip f) x ys
  reverse-foldl f x []       = refl
  reverse-foldl f x (y ∷ ys) = begin
    foldl f x (reverse (y ∷ ys)) ≡⟨ P.cong (foldl f x) (unfold-reverse y ys) ⟩
    foldl f x ((reverse ys) ∷ʳ y) ≡⟨ foldl-∷ʳ f x y (reverse ys) ⟩
    f (foldl f x (reverse ys)) y ≡⟨ P.cong (flip f y) (reverse-foldl f x ys) ⟩
    f (foldr (flip f) x ys) y    ∎
    where open P.≡-Reasoning

------------------------------------------------------------------------
-- _∷ʳ_

module _ {a} {A : Set a} where

  ∷ʳ-injective : ∀ {x y : A} xs ys →
                 xs ∷ʳ x ≡ ys ∷ʳ y → xs ≡ ys × x ≡ y
  ∷ʳ-injective []          []          refl = (refl , refl)
  ∷ʳ-injective (x ∷ xs)    (y  ∷ ys)   eq   with ∷-injective eq
  ... | refl , eq′ = Prod.map (P.cong (x ∷_)) id (∷ʳ-injective xs ys eq′)
  ∷ʳ-injective []          (_ ∷ [])    ()
  ∷ʳ-injective []          (_ ∷ _ ∷ _) ()
  ∷ʳ-injective (_ ∷ [])    []          ()
  ∷ʳ-injective (_ ∷ _ ∷ _) []          ()

  ∷ʳ-injectiveˡ : ∀ {x y : A} (xs ys : List A) → xs ∷ʳ x ≡ ys ∷ʳ y → xs ≡ ys
  ∷ʳ-injectiveˡ xs ys eq = proj₁ (∷ʳ-injective xs ys eq)

  ∷ʳ-injectiveʳ : ∀ {x y : A} (xs ys : List A) → xs ∷ʳ x ≡ ys ∷ʳ y → x ≡ y
  ∷ʳ-injectiveʳ xs ys eq = proj₂ (∷ʳ-injective xs ys eq)

------------------------------------------------------------------------
-- The list monad.

module Monad where

  left-identity : ∀ {ℓ} {A B : Set ℓ} (x : A) (f : A → List B) →
                  (return x >>= f) ≡ f x
  left-identity x f = proj₂ LM.identity (f x)

  right-identity : ∀ {a} {A : Set a} (xs : List A) →
                   (xs >>= return) ≡ xs
  right-identity []       = refl
  right-identity (x ∷ xs) = P.cong (x ∷_) (right-identity xs)

  left-zero : ∀ {ℓ} {A B : Set ℓ} (f : A → List B) → (∅ >>= f) ≡ ∅
  left-zero f = refl

  right-zero : ∀ {ℓ} {A B : Set ℓ} (xs : List A) →
               (xs >>= const ∅) ≡ ∅ {A = B}
  right-zero []       = refl
  right-zero (x ∷ xs) = right-zero xs

  private

    not-left-distributive :
      let xs = true ∷ false ∷ []; f = return; g = return in
      (xs >>= λ x → f x ∣ g x) ≢ ((xs >>= f) ∣ (xs >>= g))
    not-left-distributive ()

  right-distributive : ∀ {ℓ} {A B : Set ℓ}
                       (xs ys : List A) (f : A → List B) →
                       (xs ∣ ys >>= f) ≡ ((xs >>= f) ∣ (ys >>= f))
  right-distributive []       ys f = refl
  right-distributive (x ∷ xs) ys f = begin
    f x ∣ (xs ∣ ys >>= f)              ≡⟨ P.cong (f x ∣_) $ right-distributive xs ys f ⟩
    f x ∣ ((xs >>= f) ∣ (ys >>= f))    ≡⟨ P.sym $ LM.assoc (f x) _ _ ⟩
    ((f x ∣ (xs >>= f)) ∣ (ys >>= f))  ∎
    where open P.≡-Reasoning

  associative : ∀ {ℓ} {A B C : Set ℓ}
                (xs : List A) (f : A → List B) (g : B → List C) →
                (xs >>= λ x → f x >>= g) ≡ (xs >>= f >>= g)
  associative []       f g = refl
  associative (x ∷ xs) f g = begin
    (f x >>= g) ∣ (xs >>= λ x → f x >>= g)  ≡⟨ P.cong ((f x >>= g) ∣_) $ associative xs f g ⟩
    (f x >>= g) ∣ (xs >>= f >>= g)          ≡⟨ P.sym $ right-distributive (f x) (xs >>= f) g ⟩
    (f x ∣ (xs >>= f) >>= g)                ∎
    where open P.≡-Reasoning

  cong : ∀ {ℓ} {A B : Set ℓ} {xs₁ xs₂} {f₁ f₂ : A → List B} →
         xs₁ ≡ xs₂ → f₁ ≗ f₂ → (xs₁ >>= f₁) ≡ (xs₂ >>= f₂)
  cong {xs₁ = xs} refl f₁≗f₂ = P.cong concat (map-cong f₁≗f₂ xs)

------------------------------------------------------------------------
-- The applicative functor derived from the list monad.

-- Note that these proofs (almost) show that RawIMonad.rawIApplicative
-- is correctly defined. The proofs can be reused if proof components
-- are ever added to RawIMonad and RawIApplicative.

module Applicative where

  open P.≡-Reasoning

  private

    -- A variant of flip map.

    pam : ∀ {ℓ} {A B : Set ℓ} → List A → (A → B) → List B
    pam xs f = xs >>= return ∘ f

  -- ∅ is a left zero for _⊛_.

  left-zero : ∀ {ℓ} {A B : Set ℓ} (xs : List A) → (∅ ⊛ xs) ≡ ∅ {A = B}
  left-zero xs = begin
    ∅ ⊛ xs          ≡⟨ refl ⟩
    (∅ >>= pam xs)  ≡⟨ Monad.left-zero (pam xs) ⟩
    ∅               ∎

  -- ∅ is a right zero for _⊛_.

  right-zero : ∀ {ℓ} {A B : Set ℓ} (fs : List (A → B)) → (fs ⊛ ∅) ≡ ∅
  right-zero {ℓ} fs = begin
    fs ⊛ ∅            ≡⟨ refl ⟩
    (fs >>= pam ∅)    ≡⟨ (Monad.cong (refl {x = fs}) λ f →
                          Monad.left-zero (return ∘ f)) ⟩
    (fs >>= λ _ → ∅)  ≡⟨ Monad.right-zero fs ⟩
    ∅                 ∎

  -- _⊛_ distributes over _∣_ from the right.

  right-distributive : ∀ {ℓ} {A B : Set ℓ} (fs₁ fs₂ : List (A → B)) xs →
                       ((fs₁ ∣ fs₂) ⊛ xs) ≡ (fs₁ ⊛ xs ∣ fs₂ ⊛ xs)
  right-distributive fs₁ fs₂ xs = begin
    (fs₁ ∣ fs₂) ⊛ xs                     ≡⟨ refl ⟩
    (fs₁ ∣ fs₂ >>= pam xs)               ≡⟨ Monad.right-distributive fs₁ fs₂ (pam xs) ⟩
    (fs₁ >>= pam xs) ∣ (fs₂ >>= pam xs)  ≡⟨ refl ⟩
    (fs₁ ⊛ xs ∣ fs₂ ⊛ xs)                ∎

  -- _⊛_ does not distribute over _∣_ from the left.

  private

    not-left-distributive :
      let fs = id ∷ id ∷ []; xs₁ = true ∷ []; xs₂ = true ∷ false ∷ [] in
      (fs ⊛ (xs₁ ∣ xs₂)) ≢ (fs ⊛ xs₁ ∣ fs ⊛ xs₂)
    not-left-distributive ()

  -- Applicative functor laws.

  identity : ∀ {a} {A : Set a} (xs : List A) → (return id ⊛ xs) ≡ xs
  identity xs = begin
    return id ⊛ xs          ≡⟨⟩
    (return id >>= pam xs)  ≡⟨ Monad.left-identity id (pam xs) ⟩
    (xs >>= return)         ≡⟨ Monad.right-identity xs ⟩
    xs                      ∎

  private

    pam-lemma : ∀ {ℓ} {A B C : Set ℓ}
                (xs : List A) (f : A → B) (fs : B → List C) →
                (pam xs f >>= fs) ≡ (xs >>= λ x → fs (f x))
    pam-lemma xs f fs = begin
      (pam xs f >>= fs)                   ≡⟨ P.sym $ Monad.associative xs (return ∘ f) fs ⟩
      (xs >>= λ x → return (f x) >>= fs)  ≡⟨ Monad.cong (refl {x = xs}) (λ x → Monad.left-identity (f x) fs) ⟩
      (xs >>= λ x → fs (f x))             ∎

  composition : ∀ {ℓ} {A B C : Set ℓ}
                (fs : List (B → C)) (gs : List (A → B)) xs →
                (return _∘′_ ⊛ fs ⊛ gs ⊛ xs) ≡ (fs ⊛ (gs ⊛ xs))
  composition {ℓ} fs gs xs = begin
    return _∘′_ ⊛ fs ⊛ gs ⊛ xs                      ≡⟨⟩
    (return _∘′_ >>= pam fs >>= pam gs >>= pam xs)  ≡⟨ Monad.cong (Monad.cong (Monad.left-identity _∘′_ (pam fs))
                                                                              (λ f → refl {x = pam gs f}))
                                                                  (λ fg → refl {x = pam xs fg}) ⟩
    (pam fs _∘′_ >>= pam gs >>= pam xs)             ≡⟨ Monad.cong (pam-lemma fs _∘′_ (pam gs)) (λ _ → refl) ⟩
    ((fs >>= λ f → pam gs (f ∘′_)) >>= pam xs)     ≡⟨ P.sym $ Monad.associative fs (λ f → pam gs (_∘′_ f)) (pam xs) ⟩
    (fs >>= λ f → pam gs (f ∘′_) >>= pam xs)       ≡⟨ (Monad.cong (refl {x = fs}) λ f →
                                                        pam-lemma gs (f ∘′_) (pam xs)) ⟩
    (fs >>= λ f → gs >>= λ g → pam xs (f ∘′ g))     ≡⟨ (Monad.cong (refl {x = fs}) λ f →
                                                        Monad.cong (refl {x = gs}) λ g →
                                                        P.sym $ pam-lemma xs g (return ∘ f)) ⟩
    (fs >>= λ f → gs >>= λ g → pam (pam xs g) f)    ≡⟨ (Monad.cong (refl {x = fs}) λ f →
                                                        Monad.associative gs (pam xs) (return ∘ f)) ⟩
    (fs >>= pam (gs >>= pam xs))                    ≡⟨⟩
    fs ⊛ (gs ⊛ xs)                                  ∎

  homomorphism : ∀ {ℓ} {A B : Set ℓ} (f : A → B) x →
                 (return f ⊛ return x) ≡ return (f x)
  homomorphism f x = begin
    return f ⊛ return x            ≡⟨⟩
    (return f >>= pam (return x))  ≡⟨ Monad.left-identity f (pam (return x)) ⟩
    pam (return x) f               ≡⟨ Monad.left-identity x (return ∘ f) ⟩
    return (f x)                   ∎

  interchange : ∀ {ℓ} {A B : Set ℓ} (fs : List (A → B)) {x} →
                (fs ⊛ return x) ≡ (return (λ f → f x) ⊛ fs)
  interchange fs {x} = begin
    fs ⊛ return x                    ≡⟨⟩
    (fs >>= pam (return x))          ≡⟨ (Monad.cong (refl {x = fs}) λ f →
                                         Monad.left-identity x (return ∘ f)) ⟩
    (fs >>= λ f → return (f x))      ≡⟨⟩
    (pam fs (λ f → f x))             ≡⟨ P.sym $ Monad.left-identity (λ f → f x) (pam fs) ⟩
    (return (λ f → f x) >>= pam fs)  ≡⟨⟩
    return (λ f → f x) ⊛ fs          ∎

------------------------------------------------------------------------
-- DEPRECATED
------------------------------------------------------------------------
-- Please use `filter` and `partition` instead of `boolFilter` and
-- `boolPartition`

boolFilter-filters : ∀ {a p} {A : Set a} →
                 (P : A → Set p) (dec : Decidable P) (xs : List A) →
                 All P (boolFilter (⌊_⌋ ∘ dec) xs)
boolFilter-filters P dec []       = []
boolFilter-filters P dec (x ∷ xs) with dec x
... | yes px = px ∷ boolFilter-filters P dec xs
... | no ¬px = boolFilter-filters P dec xs

length-boolFilter : ∀ {a} {A : Set a} (p : A → Bool) xs →
                length (boolFilter p xs) ≤ length xs
length-boolFilter p xs =
  length-mapMaybe (λ x → if p x then just x else nothing) xs

boolPartition-defn : ∀ {a} {A : Set a} (p : A → Bool) →
                 boolPartition p ≗ < boolFilter p , boolFilter (not ∘ p) >
boolPartition-defn p []       = refl
boolPartition-defn p (x ∷ xs) with p x
...  | true  = P.cong (Prod.map (x ∷_) id) (boolPartition-defn p xs)
...  | false = P.cong (Prod.map id (x ∷_)) (boolPartition-defn p xs)

gfilter-just      = mapMaybe-just
gfilter-nothing   = mapMaybe-nothing
gfilter-concatMap = mapMaybe-concatMap
length-gfilter    = length-mapMaybe

right-identity-unique = ++-identityʳ-unique
left-identity-unique  = ++-identityˡ-unique
