------------------------------------------------------------------------
-- The Agda standard library
--
-- List-related properties
------------------------------------------------------------------------

-- Note that the lemmas below could be generalised to work with other
-- equalities than _≡_.

module Data.List.Properties where

open import Algebra
open import Algebra.Structures
open import Algebra.FunctionProperties
import Algebra.Monoid-solver
open import Data.Bool.Base using (Bool; false; true; not; if_then_else_)
open import Data.List as List
open import Data.List.All using (All; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product as Prod hiding (map; zip)
open import Function
import Relation.Binary.EqReasoning as EqR
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≢_; _≗_; refl)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Unary using (Decidable; ∁; ∁?)

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

  ++-assoc : Associative {A = List A} _≡_ _++_
  ++-assoc []       ys zs = refl
  ++-assoc (x ∷ xs) ys zs = P.cong (x ∷_) (++-assoc xs ys zs)

  ++-identityˡ : LeftIdentity {A = List A} _≡_ [] _++_
  ++-identityˡ xs = refl

  ++-identityʳ : RightIdentity {A = List A} _≡_ [] _++_
  ++-identityʳ []       = refl
  ++-identityʳ (x ∷ xs) = P.cong (x ∷_) (++-identityʳ xs)

  ++-identity : Identity {A = List A} _≡_ [] _++_
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
         ys ++ x ∷ xs        ≡⟨ P.sym (++-assoc ys [ x ] xs) ⟩
         (ys ++ [ x ]) ++ xs ∎)
    where open P.≡-Reasoning
  ++-identityˡ-unique {xs = x ∷ xs} (y ∷ []   ) eq | ()
  ++-identityˡ-unique {xs = x ∷ xs} (y ∷ _ ∷ _) eq | ()

  length-++ : ∀ (xs : List A) {ys} → length (xs ++ ys) ≡ length xs + length ys
  length-++ []       = refl
  length-++ (x ∷ xs) = P.cong suc (length-++ xs)

  ++-isSemigroup : IsSemigroup {A = List A} _≡_ _++_
  ++-isSemigroup = record
    { isEquivalence = P.isEquivalence
    ; assoc         = ++-assoc
    ; ∙-cong        = P.cong₂ _++_
    }

  ++-isMonoid : IsMonoid {A = List A} _≡_ _++_ []
  ++-isMonoid = record
    { isSemigroup = ++-isSemigroup
    ; identity    = ++-identity
    }

++-semigroup : ∀ {a} (A : Set a) → Semigroup _ _
++-semigroup A = record
  { Carrier  = List A
  ; _≈_      = _≡_
  ; _∙_      = _++_
  ; isSemigroup = ++-isSemigroup
  }

++-monoid : ∀ {a} (A : Set a) → Monoid _ _
++-monoid A = record
  { Carrier  = List A
  ; _≈_      = _≡_
  ; _∙_      = _++_
  ; ε        = []
  ; isMonoid = ++-isMonoid
  }

------------------------------------------------------------------------
-- zipWith

module _ {a b c} {A : Set a} {B : Set b} {C : Set c}
         (f : A → B → C) where

  zipWith-identityˡ : ∀ xs → zipWith f [] xs ≡ []
  zipWith-identityˡ []       = refl
  zipWith-identityˡ (x ∷ xs) = refl

  zipWith-identityʳ : ∀ xs → zipWith f xs [] ≡ []
  zipWith-identityʳ []       = refl
  zipWith-identityʳ (x ∷ xs) = refl

  length-zipWith : ∀ xs ys →
                   length (zipWith f xs ys) ≡ length xs ⊓ length ys
  length-zipWith []       []       = refl
  length-zipWith []       (y ∷ ys) = refl
  length-zipWith (x ∷ xs) []       = refl
  length-zipWith (x ∷ xs) (y ∷ ys) = P.cong suc (length-zipWith xs ys)

module _ {a b} {A : Set a} {B : Set b} (f : A → A → B) where

  zipWith-comm : (∀ x y → f x y ≡ f y x) →
                 ∀ xs ys → zipWith f xs ys ≡ zipWith f ys xs
  zipWith-comm f-comm []       []       = refl
  zipWith-comm f-comm []       (x ∷ ys) = refl
  zipWith-comm f-comm (x ∷ xs) []       = refl
  zipWith-comm f-comm (x ∷ xs) (y ∷ ys) =
    P.cong₂ _∷_ (f-comm x y) (zipWith-comm f-comm xs ys)

------------------------------------------------------------------------
-- unzipWith

module _ {a b c} {A : Set a} {B : Set b} {C : Set c}
         (f : A → B × C) where

  length-unzipWith₁ : ∀ xys →
                     length (proj₁ (unzipWith f xys)) ≡ length xys
  length-unzipWith₁ []        = refl
  length-unzipWith₁ (x ∷ xys) = P.cong suc (length-unzipWith₁ xys)

  length-unzipWith₂ : ∀ xys →
                     length (proj₂ (unzipWith f xys)) ≡ length xys
  length-unzipWith₂ []        = refl
  length-unzipWith₂ (x ∷ xys) = P.cong suc (length-unzipWith₂ xys)

  zipWith-unzipWith : (g : B → C → A) → uncurry′ g ∘ f ≗ id →
                      uncurry′ (zipWith g) ∘ (unzipWith f)  ≗ id
  zipWith-unzipWith g f∘g≗id []       = refl
  zipWith-unzipWith g f∘g≗id (x ∷ xs) =
    P.cong₂ _∷_ (f∘g≗id x) (zipWith-unzipWith g f∘g≗id xs)

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
      reverse ys ++ y ∷ xs          ≡⟨ P.sym (++-assoc (reverse ys) _ _) ⟩
      (reverse ys ∷ʳ y) ++ xs       ≡⟨ P.sym $ P.cong (_++ xs) (unfold-reverse y ys) ⟩
      reverse (y ∷ ys) ++ xs        ∎

  reverse-++-commute : (xs ys : List A) →
                       reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
  reverse-++-commute []       ys = P.sym (++-identityʳ _)
  reverse-++-commute (x ∷ xs) ys = begin
    reverse (x ∷ xs ++ ys)               ≡⟨ unfold-reverse x (xs ++ ys) ⟩
    reverse (xs ++ ys) ++ [ x ]          ≡⟨ P.cong (_++ [ x ]) (reverse-++-commute xs ys) ⟩
    (reverse ys ++ reverse xs) ++ [ x ]  ≡⟨ ++-assoc (reverse ys) _ _ ⟩
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
-- Modules for reasoning about propositional equality of lists

-- A module for automatically solving propositional equivalences
module List-solver {a} {A : Set a} =
  Algebra.Monoid-solver (++-monoid A) renaming (id to nil)

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
