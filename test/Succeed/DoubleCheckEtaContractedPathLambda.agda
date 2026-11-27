-- Eta-contracted path lambdas and --double-check.
--
-- instantiateFull eta-contracts a lambda without looking at its type.
-- Thus it also contracts a path lambda λ i → f i to f, where
-- f : (i : I) → A is a function, not a path.
-- The type checker and the conversion checker accept such terms.
-- The internal checker (CheckInternal) rejected them, and the double
-- check of meta solutions uses the internal checker.
--
-- The cubical library failed in these ways, in
-- Cubical.Foundations.Prelude and Cubical.Foundations.GroupoidLaws.

{-# OPTIONS --cubical --double-check #-}

module DoubleCheckEtaContractedPathLambda where

open import Agda.Primitive using (Level)
open import Agda.Primitive.Cubical renaming (primTransp to transp)
open import Agda.Builtin.Cubical.Path

variable
  ℓ : Level

------------------------------------------------------------------------
-- Case 1: an IApply elimination whose head has a function type.
--
-- The type of toPathP contains the path lambda λ i → A i, and
-- instantiateFull contracts it to A.  When Agda unfolds transport,
-- it substitutes A for p in p i, and p i is an IApply.
-- The double check of the meta solution failed with:
--
--   I → Set ℓ should be a Path or PathP type, but it isn't
--   when checking that the solution transp (λ i → B i) i0 b0 of
--   metavariable _x_44 has the expected type B i1

transport : {A B : Set ℓ} → A ≡ B → A → B
transport p a = transp (λ i → p i) i0 a

postulate
  toPathP : {A : I → Set ℓ} {x : A i0} {y : A i1}
          → transport (λ i → A i) x ≡ y → PathP A x y

isProp : Set ℓ → Set ℓ
isProp A = (x y : A) → x ≡ y

isProp→PathP : {B : I → Set ℓ} → ((i : I) → isProp (B i))
             → (b0 : B i0) (b1 : B i1)
             → PathP B b0 b1
isProp→PathP hB b0 b1 = toPathP (hB _ _ _)

-- The same with a simpler example.
-- The double check of the meta solution failed with:
--
--   I → B should be a Path or PathP type, but it isn't
--   when checking that the solution h x i of metavariable _H_27 has
--   the expected type B

postulate
  P  : {A B : Set} {f g : A → B} → ((x : A) → f x ≡ g x) → Set
  mk : {A B : Set} {f g : A → B} (H : (x : A) → f x ≡ g x) → P H

test₁ : {A B : Set} (h : A → I → B)
      → P {f = λ x → h x i0} {g = λ x → h x i1} (λ x i → h x i)
test₁ h = mk _

------------------------------------------------------------------------
-- Case 2: a term of function type where a path type is expected.
--
-- The type of p contains the path lambda λ i i₁ → c i i0 i₁.
-- instantiateFull contracts the inner lambda λ i₁ → c i i0 i₁
-- to c i i0 : I → A, but this term has to have the path type
-- c i i0 i0 ≡ c i i0 i1.
-- The double check of the meta solution failed with:
--
--   The type
--     I → A
--   is not a subtype of
--     c i i0 i0 ≡ c i i0 i1
--   when checking that the solution p l i k of metavariable _99 has the
--   expected type A

Square : {A : Set ℓ} {a₀₀ a₀₁ : A} (a₀₋ : a₀₀ ≡ a₀₁)
         {a₁₀ a₁₁ : A} (a₁₋ : a₁₀ ≡ a₁₁)
         (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁) → Set ℓ
Square a₀₋ a₁₋ a₋₀ a₋₁ = PathP (λ i → a₋₀ i ≡ a₋₁ i) a₀₋ a₁₋

cube-comp₋₀₋ : {A : Set ℓ} (c : I → I → I → A) {a' : Square _ _ _ _}
             → (λ i i₁ → c i i0 i₁) ≡ a' → I → I → I → A
cube-comp₋₀₋ c p i j k =
  primHComp (λ l → λ { (j = i0) → p l i k
                     ; (j = i1) → c i i1 k })
            (c i j k)

------------------------------------------------------------------------
-- Case 3: as case 2, but with two path lambdas.
--
-- instantiateFull contracts λ i i₁ → c i0 i i₁ to c i0 : I → I → A,
-- but this term has to have a path type of path types.
-- The double check of the meta solution failed with:
--
--   The type
--     I → A
--   is not a subtype of
--     c i0 i i0 ≡ c i0 i i1
--   when checking that the solution p l j k of metavariable _51 has the
--   expected type A

cube-comp₀₋₋ : {A : Set ℓ} (c : I → I → I → A) {a' : Square _ _ _ _}
             → (λ i i₁ → c i0 i i₁) ≡ a' → I → I → I → A
cube-comp₀₋₋ c p i j k =
  primHComp (λ l → λ { (i = i0) → p l j k
                     ; (i = i1) → c i1 j k })
            (c i j k)

------------------------------------------------------------------------
-- Case 4: a path lambda under a function lambda.
--
-- instantiateFull contracts λ x i → h x i to h : A → I → B,
-- but this term has to have the type (x : A) → h x i0 ≡ h x i1.
-- The double check of the meta solution failed with:
--
--   The type
--     I → B
--   is not a subtype of
--     h x i0 ≡ h x i1
--   when checking that the solution P h of metavariable _X_31 has the
--   expected type Set

postulate
  Box  : {X : Set} → X → Set
  wrap : {X : Set} (x : X) → Box x

test₄ : {A B : Set} (h : A → I → B)
      → Box {X = P {f = λ x → h x i0} {g = λ x → h x i1} (λ x i → h x i)}
            (mk (λ x i → h x i))
test₄ h = wrap _
