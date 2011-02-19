------------------------------------------------------------------------
-- Properties related to bag and set equality
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

-- Bag and set equality are defined in Data.List.Any.

module Data.List.Any.BagAndSetEquality where

open import Algebra
open import Algebra.FunctionProperties
open import Category.Monad
open import Data.Empty
open import Data.List as List
import Data.List.Properties as LP
open import Data.List.Any as Any using (Any); open Any.Any
open import Data.List.Any.Properties
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Function
open import Function.Equality using (_⟨$⟩_)
import Function.Equivalence as FE
open import Function.Inverse as Inv using (_⇿_; module Inverse)
open import Function.Inverse.TypeIsomorphisms
open import Level
open import Relation.Binary
import Relation.Binary.EqReasoning as EqR
import Relation.Binary.Sigma.Pointwise as Σ
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≗_; _with-≡_)
open import Relation.Nullary

open Any.Membership-≡
private
  module Eq {k a} {A : Set a} = Setoid ([ k ]-Equality A)
  module ×⊎ {k ℓ} = CommutativeSemiring (×⊎-CommutativeSemiring k ℓ)
  open module ListMonad {ℓ} = RawMonad (List.monad {ℓ = ℓ})
  module ListMonoid {a} {A : Set a} = Monoid (List.monoid A)

-- _++_ and [] form a commutative monoid, with either bag or set
-- equality as the underlying equality.

commutativeMonoid : ∀ {a} → Kind → Set a → CommutativeMonoid _ _
commutativeMonoid {a} k A = record
  { Carrier             = List A
  ; _≈_                 = λ xs ys → xs ≈[ k ] ys
  ; _∙_                 = _++_
  ; ε                   = []
  ; isCommutativeMonoid = record
    { isSemigroup = record
      { isEquivalence = Eq.isEquivalence
      ; assoc         = λ xs ys zs →
                          Eq.reflexive (ListMonoid.assoc xs ys zs)
      ; ∙-cong        = λ {xs₁ xs₂ xs₃ xs₄} xs₁≈xs₂ xs₃≈xs₄ {x} →
                          x ∈ xs₁ ++ xs₃       ⇿⟨ sym $ ++⇿ {a = a} {p = a} ⟩
                          (x ∈ xs₁ ⊎ x ∈ xs₃)  ≈⟨ xs₁≈xs₂ ⟨ ×⊎.+-cong ⟩ xs₃≈xs₄ ⟩
                          (x ∈ xs₂ ⊎ x ∈ xs₄)  ⇿⟨ ++⇿ {a = a} {p = a} ⟩
                          x ∈ xs₂ ++ xs₄       ∎
      }
    ; identityˡ = λ xs {x} → x ∈ xs ∎
    ; comm      = λ xs ys {x} →
                    x ∈ xs ++ ys  ⇿⟨ ++⇿++ {a = a} {p = a} xs ys ⟩
                    x ∈ ys ++ xs  ∎
    }
  }
  where open Inv.EquationalReasoning

-- The only list which is bag or set equal to the empty list is the
-- empty list itself.

empty-unique : ∀ {k a} {A : Set a} {xs : List A} →
               xs ≈[ k ] [] → xs ≡ []
empty-unique {xs = []}    _    = P.refl
empty-unique {xs = _ ∷ _} ∷≈[]
  with FE.Equivalent.to (Inv.⇒⇔ ∷≈[]) ⟨$⟩ here P.refl
... | ()

-- _++_ is idempotent (under set equality).

++-idempotent : ∀ {a} {A : Set a} →
                Idempotent (λ (xs ys : List A) → xs ≈[ set ] ys) _++_
++-idempotent {a} xs {x} =
  x ∈ xs ++ xs  ≈⟨ FE.equivalent ([ id , id ]′ ∘ _⟨$⟩_ (Inverse.from $ ++⇿ {a = a} {p = a}))
                                 (_⟨$⟩_ (Inverse.to $ ++⇿ {a = a} {p = a}) ∘ inj₁) ⟩
  x ∈ xs        ∎
  where open Inv.EquationalReasoning

-- List.map is a congruence.

map-cong : ∀ {ℓ k} {A B : Set ℓ} {f₁ f₂ : A → B} {xs₁ xs₂} →
           f₁ ≗ f₂ → xs₁ ≈[ k ] xs₂ →
           List.map f₁ xs₁ ≈[ k ] List.map f₂ xs₂
map-cong {ℓ} {f₁ = f₁} {f₂} {xs₁} {xs₂} f₁≗f₂ xs₁≈xs₂ {x} =
  x ∈ List.map f₁ xs₁       ⇿⟨ sym $ map⇿ {a = ℓ} {b = ℓ} {p = ℓ} ⟩
  Any (λ y → x ≡ f₁ y) xs₁  ≈⟨ Any-cong (Inv.⇿⇒ ∘ helper) xs₁≈xs₂ ⟩
  Any (λ y → x ≡ f₂ y) xs₂  ⇿⟨ map⇿ {a = ℓ} {b = ℓ} {p = ℓ} ⟩
  x ∈ List.map f₂ xs₂       ∎
  where
  open Inv.EquationalReasoning

  helper : ∀ y → x ≡ f₁ y ⇿ x ≡ f₂ y
  helper y = record
    { to         = P.→-to-⟶ (λ x≡f₁y → P.trans x≡f₁y (        f₁≗f₂ y))
    ; from       = P.→-to-⟶ (λ x≡f₂y → P.trans x≡f₂y (P.sym $ f₁≗f₂ y))
    ; inverse-of = record
      { left-inverse-of  = λ _ → P.proof-irrelevance _ _
      ; right-inverse-of = λ _ → P.proof-irrelevance _ _
      }
    }

-- concat is a congruence.

concat-cong : ∀ {a k} {A : Set a} {xss₁ xss₂ : List (List A)} →
              xss₁ ≈[ k ] xss₂ → concat xss₁ ≈[ k ] concat xss₂
concat-cong {a} {xss₁ = xss₁} {xss₂} xss₁≈xss₂ {x} =
  x ∈ concat xss₁         ⇿⟨ sym $ concat⇿ {a = a} {p = a} ⟩
  Any (Any (_≡_ x)) xss₁  ≈⟨ Any-cong (λ _ → _ ∎) xss₁≈xss₂ ⟩
  Any (Any (_≡_ x)) xss₂  ⇿⟨ concat⇿ {a = a} {p = a} ⟩
  x ∈ concat xss₂         ∎
  where open Inv.EquationalReasoning

-- The list monad's bind is a congruence.

>>=-cong : ∀ {ℓ k} {A B : Set ℓ} {xs₁ xs₂} {f₁ f₂ : A → List B} →
           xs₁ ≈[ k ] xs₂ → (∀ x → f₁ x ≈[ k ] f₂ x) →
           (xs₁ >>= f₁) ≈[ k ] (xs₂ >>= f₂)
>>=-cong {ℓ} {xs₁ = xs₁} {xs₂} {f₁} {f₂} xs₁≈xs₂ f₁≈f₂ {x} =
  x ∈ (xs₁ >>= f₁)          ⇿⟨ sym $ >>=⇿ {ℓ = ℓ} {p = ℓ} ⟩
  Any (λ y → x ∈ f₁ y) xs₁  ≈⟨ Any-cong (λ x → f₁≈f₂ x) xs₁≈xs₂ ⟩
  Any (λ y → x ∈ f₂ y) xs₂  ⇿⟨ >>=⇿ {ℓ = ℓ} {p = ℓ} ⟩
  x ∈ (xs₂ >>= f₂)          ∎
  where open Inv.EquationalReasoning

-- _⊛_ is a congruence.

⊛-cong : ∀ {ℓ k} {A B : Set ℓ} {fs₁ fs₂ : List (A → B)} {xs₁ xs₂} →
         fs₁ ≈[ k ] fs₂ → xs₁ ≈[ k ] xs₂ → fs₁ ⊛ xs₁ ≈[ k ] fs₂ ⊛ xs₂
⊛-cong fs₁≈fs₂ xs₁≈xs₂ =
  >>=-cong fs₁≈fs₂ λ f →
  >>=-cong xs₁≈xs₂ λ x →
  _ ∎
  where open Inv.EquationalReasoning

-- _⊗_ is a congruence.

⊗-cong : ∀ {ℓ k} {A B : Set ℓ} {xs₁ xs₂ : List A} {ys₁ ys₂ : List B} →
         xs₁ ≈[ k ] xs₂ → ys₁ ≈[ k ] ys₂ →
         (xs₁ ⊗ ys₁) ≈[ k ] (xs₂ ⊗ ys₂)
⊗-cong {ℓ} xs₁≈xs₂ ys₁≈ys₂ =
  ⊛-cong (⊛-cong (Eq.refl {x = [ _,_ {a = ℓ} {b = ℓ} ]})
                 xs₁≈xs₂)
         ys₁≈ys₂

-- The list monad's bind distributes from the left over _++_.

>>=-left-distributive :
  ∀ {ℓ} {A B : Set ℓ} (xs : List A) {f g : A → List B} →
  (xs >>= λ x → f x ++ g x) ≈[ bag ] (xs >>= f) ++ (xs >>= g)
>>=-left-distributive {ℓ} xs {f} {g} {y} =
  y ∈ (xs >>= λ x → f x ++ g x)                      ⇿⟨ sym $ >>=⇿ {ℓ = ℓ} {p = ℓ} ⟩
  Any (λ x → y ∈ f x ++ g x) xs                      ⇿⟨ sym (Any-cong (λ _ → ++⇿ {a = ℓ} {p = ℓ}) (_ ∎)) ⟩
  Any (λ x → y ∈ f x ⊎ y ∈ g x) xs                   ⇿⟨ sym $ ⊎⇿ {a = ℓ} {p = ℓ} {q = ℓ} ⟩
  (Any (λ x → y ∈ f x) xs ⊎ Any (λ x → y ∈ g x) xs)  ⇿⟨ >>=⇿ {ℓ = ℓ} {p = ℓ} ⟨ ×⊎.+-cong {ℓ = ℓ} ⟩ >>=⇿ {ℓ = ℓ} {p = ℓ} ⟩
  (y ∈ (xs >>= f) ⊎ y ∈ (xs >>= g))                  ⇿⟨ ++⇿ {a = ℓ} {p = ℓ} ⟩
  y ∈ (xs >>= f) ++ (xs >>= g)                       ∎
  where open Inv.EquationalReasoning

-- The same applies to _⊛_.

⊛-left-distributive :
  ∀ {ℓ} {A B : Set ℓ} (fs : List (A → B)) xs₁ xs₂ →
  fs ⊛ (xs₁ ++ xs₂) ≈[ bag ] (fs ⊛ xs₁) ++ (fs ⊛ xs₂)
⊛-left-distributive {B = B} fs xs₁ xs₂ = begin
  fs ⊛ (xs₁ ++ xs₂)                         ≡⟨ P.refl ⟩
  (fs >>= λ f → xs₁ ++ xs₂ >>= return ∘ f)  ≡⟨ (LP.Monad.cong (P.refl {x = fs}) λ f →
                                                LP.Monad.right-distributive xs₁ xs₂ (return ∘ f)) ⟩
  (fs >>= λ f → (xs₁ >>= return ∘ f) ++
                (xs₂ >>= return ∘ f))       ≈⟨ >>=-left-distributive fs ⟩

  (fs >>= λ f → xs₁ >>= return ∘ f) ++
  (fs >>= λ f → xs₂ >>= return ∘ f)         ≡⟨ P.refl ⟩

  (fs ⊛ xs₁) ++ (fs ⊛ xs₂)                  ∎
  where open EqR ([ bag ]-Equality B)

private

  -- If x ∷ xs is set equal to x ∷ ys, then xs and ys are not
  -- necessarily set equal.

  ¬-drop-cons :
    ∀ {a} {A : Set a} {x : A} →
    ¬ (∀ {xs ys} → x ∷ xs ≈[ set ] x ∷ ys → xs ≈[ set ] ys)
  ¬-drop-cons {x = x} drop-cons
    with FE.Equivalent.to x≈[] ⟨$⟩ here P.refl
    where
    x,x≈x :  (x ∷ x ∷ []) ≈[ set ] [ x ]
    x,x≈x = ++-idempotent [ x ]

    x≈[] : [ x ] ≈[ set ] []
    x≈[] = drop-cons x,x≈x
  ... | ()

-- However, the corresponding property does hold for bag equality.

drop-cons : ∀ {a} {A : Set a} {x : A} {xs ys} →
            x ∷ xs ≈[ bag ] x ∷ ys → xs ≈[ bag ] ys
drop-cons {A = A} {x} {xs} {ys} x∷xs≈x∷ys {z} =
  z ∈ xs                                      ⇿⟨ lemma xs ⟩
  (∃ λ (z∈x∷xs : z ∈ x ∷ xs) → There z∈x∷xs)  ⇿⟨ Σ.⇿ x∷xs≈x∷ys′ x∷xs≈x∷ys′-preserves-There ⟩
  (∃ λ (z∈x∷ys : z ∈ x ∷ ys) → There z∈x∷ys)  ⇿⟨ sym $ lemma ys ⟩
  z ∈ ys                                      ∎
  where
  open Inv.EquationalReasoning

  -- Inhabited for there but not here.

  There : ∀ {z : A} {xs} → z ∈ xs → Set
  There (here  _) = ⊥
  There (there _) = ⊤

  -- There is proof irrelevant.

  proof-irrelevance : ∀ {z xs} {z∈xs : z ∈ xs}
                      (p q : There z∈xs) → p ≡ q
  proof-irrelevance {z∈xs = here  _} () ()
  proof-irrelevance {z∈xs = there _} _  _  = P.refl

  -- An isomorphism.

  lemma : ∀ xs → z ∈ xs ⇿ (∃ λ (z∈x∷xs : z ∈ x ∷ xs) → There z∈x∷xs)
  lemma xs = record
    { to         = P.→-to-⟶ to
    ; from       = P.→-to-⟶ from
    ; inverse-of = record
      { left-inverse-of  = λ _ → P.refl
      ; right-inverse-of = to∘from
      }
    }
    where
    to : z ∈ xs → (∃ λ (z∈x∷xs : z ∈ x ∷ xs) → There z∈x∷xs)
    to z∈xs = (there z∈xs , _)

    from : (∃ λ (z∈x∷xs : z ∈ x ∷ xs) → There z∈x∷xs) → z ∈ xs
    from (here  z≡x  , ())
    from (there z∈xs , _) = z∈xs

    to∘from : ∀ p → to (from p) ≡ p
    to∘from (here  z≡x  , ())
    to∘from (there z∈xs , _) = P.refl

  -- The isomorphisms x∷xs≈x∷ys may not preserve There, because they
  -- could map here P.refl to something other than here P.refl.
  -- However, we can construct isomorphisms which do preserve There:

  x∷xs≈x∷ys′ : x ∷ xs ≈[ bag ] x ∷ ys
  x∷xs≈x∷ys′ = record
    { to         = P.→-to-⟶ $ f           x∷xs≈x∷ys
    ; from       = P.→-to-⟶ $ f $ Inv.sym x∷xs≈x∷ys
    ; inverse-of = record
      { left-inverse-of  = f∘f           x∷xs≈x∷ys
      ; right-inverse-of = f∘f $ Inv.sym x∷xs≈x∷ys
      }
    }
    where
    f : ∀ {xs ys} → x ∷ xs ≈[ bag ] x ∷ ys →
        ∀ {z} → z ∈ x ∷ xs → z ∈ x ∷ ys
    f x∷xs≈x∷ys (here P.refl) = here P.refl
    f x∷xs≈x∷ys (there z∈xs)  with Inverse.to x∷xs≈x∷ys ⟨$⟩ there z∈xs
    ... | there z∈ys  = there z∈ys
    ... | here P.refl = Inverse.to x∷xs≈x∷ys ⟨$⟩ here P.refl

    f∘f : ∀ {xs ys}
          (x∷xs≈x∷ys : x ∷ xs ≈[ bag ] x ∷ ys) →
          ∀ {z} (p : z ∈ x ∷ xs) →
          f (Inv.sym x∷xs≈x∷ys) (f x∷xs≈x∷ys p) ≡ p
    f∘f x∷xs≈x∷ys (here P.refl) = P.refl
    f∘f x∷xs≈x∷ys (there z∈xs)
      with Inverse.to x∷xs≈x∷ys ⟨$⟩ there z∈xs
         | Inverse.left-inverse-of x∷xs≈x∷ys (there z∈xs)
    ... | there z∈ys  | left rewrite left = P.refl
    ... | here P.refl | left
      with Inverse.to x∷xs≈x∷ys ⟨$⟩ here P.refl
         | Inverse.left-inverse-of x∷xs≈x∷ys (here P.refl)
    ... | there z∈xs′  | left′ rewrite left′ = left
    ... | here  P.refl | left′ rewrite left′ = left

  x∷xs≈x∷ys′-preserves-There :
    ∀ {z} {z∈x∷xs : z ∈ x ∷ xs} →
    There z∈x∷xs ⇿ There (Inverse.to x∷xs≈x∷ys′ ⟨$⟩ z∈x∷xs)
  x∷xs≈x∷ys′-preserves-There {z∈x∷xs = z∈x∷xs} = record
    { to         = P.→-to-⟶ $ to   z∈x∷xs
    ; from       = P.→-to-⟶ $ from z∈x∷xs
    ; inverse-of = record
      { left-inverse-of  = λ _ → proof-irrelevance _ _
      ; right-inverse-of = λ _ → proof-irrelevance _ _
      }
    }
    where
    open P.≡-Reasoning renaming (_∎ to _□)

    to : ∀ {z} (z∈x∷xs : z ∈ x ∷ xs) →
         There z∈x∷xs → There (Inverse.to x∷xs≈x∷ys′ ⟨$⟩ z∈x∷xs)
    to (here  _)  ()
    to (there z∈) _  with P.inspect (Inverse.to x∷xs≈x∷ys ⟨$⟩ there z∈)
    ... | there _     with-≡ eq rewrite eq = _
    ... | here P.refl with-≡ eq rewrite eq
      with P.inspect (Inverse.to x∷xs≈x∷ys ⟨$⟩ here P.refl)
    ... | there _     with-≡ eq′ rewrite eq′ = _
    ... | here P.refl with-≡ eq′ rewrite eq′
      with begin
        there z∈                                                           ≡⟨ P.sym $ Inverse.left-inverse-of x∷xs≈x∷ys _ ⟩
        Inverse.from x∷xs≈x∷ys ⟨$⟩ (Inverse.to x∷xs≈x∷ys ⟨$⟩ there z∈)     ≡⟨ P.cong (_⟨$⟩_ (Inverse.from x∷xs≈x∷ys)) eq ⟩
        Inverse.from x∷xs≈x∷ys ⟨$⟩ here P.refl                             ≡⟨ P.cong (_⟨$⟩_ (Inverse.from x∷xs≈x∷ys)) (P.sym eq′) ⟩
        Inverse.from x∷xs≈x∷ys ⟨$⟩ (Inverse.to x∷xs≈x∷ys ⟨$⟩ here P.refl)  ≡⟨ Inverse.left-inverse-of x∷xs≈x∷ys _ ⟩
        Any.here {xs = xs} (P.refl {x = x})                                □
    ... | ()

    from : ∀ {z} (z∈x∷xs : z ∈ x ∷ xs) →
           There (Inverse.to x∷xs≈x∷ys′ ⟨$⟩ z∈x∷xs) → There z∈x∷xs
    from (here P.refl) ()
    from (there z∈xs)  _  = _
