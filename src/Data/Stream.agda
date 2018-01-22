------------------------------------------------------------------------
-- The Agda standard library
--
-- Streams
------------------------------------------------------------------------

module Data.Stream where

open import Coinduction
open import Data.Colist using (Colist; []; _∷_)
open import Data.Vec    using (Vec;    []; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)

------------------------------------------------------------------------
-- The type

infixr 5 _∷_

data Stream {a} (A : Set a) : Set a where
  _∷_ : (x : A) (xs : ∞ (Stream A)) → Stream A

{-# FOREIGN GHC
  data AgdaStream a = Cons a (MAlonzo.RTE.Inf (AgdaStream a))
  #-}
{-# COMPILE GHC Stream = data AgdaStream (Cons) #-}

------------------------------------------------------------------------
-- Some operations

head : ∀ {a} {A : Set a} → Stream A → A
head (x ∷ xs) = x

tail : ∀ {a} {A : Set a} → Stream A → Stream A
tail (x ∷ xs) = ♭ xs

map : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → Stream A → Stream B
map f (x ∷ xs) = f x ∷ ♯ map f (♭ xs)

zipWith : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
          (A → B → C) → Stream A → Stream B → Stream C
zipWith _∙_ (x ∷ xs) (y ∷ ys) = (x ∙ y) ∷ ♯ zipWith _∙_ (♭ xs) (♭ ys)

take : ∀ {a} {A : Set a} n → Stream A → Vec A n
take zero    xs       = []
take (suc n) (x ∷ xs) = x ∷ take n (♭ xs)

drop : ∀ {a} {A : Set a} → ℕ → Stream A → Stream A
drop zero    xs       = xs
drop (suc n) (x ∷ xs) = drop n (♭ xs)

repeat : ∀ {a} {A : Set a} → A → Stream A
repeat x = x ∷ ♯ repeat x

iterate : ∀ {a} {A : Set a} → (A → A) → A → Stream A
iterate f x = x ∷ ♯ iterate f (f x)

-- Interleaves the two streams.

infixr 5 _⋎_

_⋎_ : ∀ {a} {A : Set a} → Stream A → Stream A → Stream A
(x ∷ xs) ⋎ ys = x ∷ ♯ (ys ⋎ ♭ xs)

mutual

  -- Takes every other element from the stream, starting with the
  -- first one.

  evens : ∀ {a} {A : Set a} → Stream A → Stream A
  evens (x ∷ xs) = x ∷ ♯ odds (♭ xs)

  -- Takes every other element from the stream, starting with the
  -- second one.

  odds : ∀ {a} {A : Set a} → Stream A → Stream A
  odds (x ∷ xs) = evens (♭ xs)

toColist : ∀ {a} {A : Set a} → Stream A → Colist A
toColist (x ∷ xs) = x ∷ ♯ toColist (♭ xs)

lookup : ∀ {a} {A : Set a} → ℕ → Stream A → A
lookup zero    (x ∷ xs) = x
lookup (suc n) (x ∷ xs) = lookup n (♭ xs)

infixr 5 _++_

_++_ : ∀ {a} {A : Set a} → Colist A → Stream A → Stream A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ ♯ (♭ xs ++ ys)

------------------------------------------------------------------------
-- Equality and other relations

-- xs ≈ ys means that xs and ys are equal.

infix 4 _≈_

data _≈_ {a} {A : Set a} : Stream A → Stream A → Set a where
  _∷_ : ∀ {x y xs ys}
        (x≡ : x ≡ y) (xs≈ : ∞ (♭ xs ≈ ♭ ys)) → x ∷ xs ≈ y ∷ ys

-- x ∈ xs means that x is a member of xs.

infix 4 _∈_

data _∈_ {a} {A : Set a} : A → Stream A → Set a where
  here  : ∀ {x   xs}                   → x ∈ x ∷ xs
  there : ∀ {x y xs} (x∈xs : x ∈ ♭ xs) → x ∈ y ∷ xs

-- xs ⊑ ys means that xs is a prefix of ys.

infix 4 _⊑_

data _⊑_ {a} {A : Set a} : Colist A → Stream A → Set a where
  []  : ∀ {ys}                            → []     ⊑ ys
  _∷_ : ∀ x {xs ys} (p : ∞ (♭ xs ⊑ ♭ ys)) → x ∷ xs ⊑ x ∷ ys

------------------------------------------------------------------------
-- Some proofs

setoid : ∀ {a} → Set a → Setoid _ _
setoid A = record
  { Carrier       = Stream A
  ; _≈_           = _≈_ {A = A}
  ; isEquivalence = record
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }
  }
  where
  refl : Reflexive _≈_
  refl {_ ∷ _} = P.refl ∷ ♯ refl

  sym : Symmetric _≈_
  sym (x≡ ∷ xs≈) = P.sym x≡ ∷ ♯ sym (♭ xs≈)

  trans : Transitive _≈_
  trans (x≡ ∷ xs≈) (y≡ ∷ ys≈) = P.trans x≡ y≡ ∷ ♯ trans (♭ xs≈) (♭ ys≈)

head-cong : ∀ {a} {A : Set a} {xs ys : Stream A} → xs ≈ ys → head xs ≡ head ys
head-cong (x≡ ∷ _) = x≡

tail-cong : ∀ {a} {A : Set a} {xs ys : Stream A} → xs ≈ ys → tail xs ≈ tail ys
tail-cong (_ ∷ xs≈) = ♭ xs≈

map-cong : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) {xs ys} →
           xs ≈ ys → map f xs ≈ map f ys
map-cong f (x≡ ∷ xs≈) = P.cong f x≡ ∷ ♯ map-cong f (♭ xs≈)

zipWith-cong : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
               (_∙_ : A → B → C) {xs xs′ ys ys′} →
               xs ≈ xs′ → ys ≈ ys′ →
               zipWith _∙_ xs ys ≈ zipWith _∙_ xs′ ys′
zipWith-cong _∙_ (x≡ ∷ xs≈) (y≡ ∷ ys≈) =
  P.cong₂ _∙_ x≡ y≡ ∷ ♯ zipWith-cong _∙_ (♭ xs≈) (♭ ys≈)

infixr 5 _⋎-cong_

_⋎-cong_ : ∀ {a} {A : Set a} {xs xs′ ys ys′ : Stream A} →
           xs ≈ xs′ → ys ≈ ys′ → xs ⋎ ys ≈ xs′ ⋎ ys′
(x ∷ xs≈) ⋎-cong ys≈ = x ∷ ♯ (ys≈ ⋎-cong ♭ xs≈)
