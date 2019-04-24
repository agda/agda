{-# OPTIONS --cubical #-}
module CubicalPrims where

open import Agda.Primitive renaming (_⊔_ to ℓ-max)
open import Agda.Primitive.Cubical renaming (primIMin to _∧_; primIMax to _∨_; primINeg to ~_; isOneEmpty to empty)
open import Agda.Builtin.Bool
open import Agda.Builtin.Cubical.Sub renaming (Sub to _[_↦_]; primSubOut to ouc)
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Cubical.Id renaming (primIdJ to J)
open import Agda.Builtin.Cubical.Glue renaming (primGlue to Glue; prim^glue to glue; prim^unglue to unglue)
open import Agda.Builtin.Sigma
open import Agda.Builtin.List
open Helpers

module _ {ℓ} {A : Set ℓ} where
  trans : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans {x = x} p q i = primComp (λ _ → A) (λ { j (i = i0) → x
                                              ; j (i = i1) → q j }) (p i)

module _ {ℓ ℓ'} {A : Set ℓ} {x : A}
         (P : ∀ y → x ≡ y → Set ℓ') (d : P x ((λ i → x))) where
  pathJ : (y : A) → (p : x ≡ y) → P y p
  pathJ _ p = primTransp (λ i →  P (p i) (\ j → p (i ∧ j))) i0 d

module DerivedComp where
  forward : (la : I → Level) (A : ∀ i → Set (la i)) (r : I) → A r → A i1
  forward la A r x = primTransp (\ i → A (i ∨ r)) r x

  module _ (la : I → Level) (A : ∀ i → Set (la i)) (φ : I) (u : ∀ i → Partial φ (A i)) (u0 : A i0 [ φ ↦ u i0 ]) where
    comp : A i1
    comp = primHComp (\ i → \ { (φ = i1) → forward la A i (u i itIsOne) }) (forward la A i0 (ouc u0))

    comp-test : comp ≡ primComp A u (ouc u0)
    comp-test = refl

test-sym : ∀ {ℓ} {A : Set ℓ} → {x y : A} → (p : x ≡ y) → sym (sym p) ≡ p
test-sym p = refl

transpFill : ∀ {ℓ} {A' : Set ℓ} (φ : I)
               (A : (i : I) → Set ℓ [ φ ↦ (\ _ → A') ]) →
               (u0 : ouc (A i0)) →
               PathP (λ i → ouc (A i)) u0 (primTransp (λ i → ouc (A i)) φ u0)
transpFill φ A u0 i = primTransp (\ j → ouc (A (i ∧ j))) (~ i ∨ φ) u0


test-bool : (p : true ≡ false) → Bool
test-bool p = primComp (λ _ → Bool) {φ = i1} (λ j → λ _ → p j) true

-- cannot reduce to true, because it's already reducing to false.
test-bool-beta : ∀ p → test-bool p ≡ false
test-bool-beta p = refl

etaExpand : ∀ {ℓ} {A : Set ℓ} {x y : A} → (p : x ≡ y) → x ≡ y
etaExpand p = λ z → p z

etaEq : ∀ {ℓ} {A : Set ℓ} {x y : A} → (p : x ≡ y) → p ≡ etaExpand p
etaEq p = refl


module IntervalEquations where
  postulate
    P : I → Set
  test-0 : (P (~ i0) ≡ P i1)
  test-0 = refl
  test-1 : P (~ i1) ≡ P i0
  test-1 = refl
  test-2 : ∀ {i j} → P (~ (i ∧ j)) ≡ P (~ i ∨ ~ j)
  test-2 = refl
  test-3 : ∀ {i j} → P (~ (i ∨ j)) ≡ P (~ i ∧ ~ j)
  test-3 = refl
  test-4 : ∀ {i} → P (~ (~ i)) ≡ P i
  test-4 = refl

  test-5 : ∀ {i} → P (_∧_ i0 i) ≡ P i0
  test-5 = refl

  test-52 : ∀ {i} → P (_∧_ i i) ≡ P i
  test-52 = refl

  test-53 : ∀ {i j} → P (i ∧ j) ≡ P (j ∧ i)
  test-53 = refl

  test-n6 : ∀ {i} → P (i1 ∧ i) ≡ P i
  test-n6 = refl

  test-n7 : ∀ {i} → P (i ∧ i0) ≡ P i0
  test-n7 = refl

  test-n8 : ∀ {i} → P (i ∧ i1) ≡ P i
  test-n8 = refl

reflId : ∀ {l} {A : Set l} {x : A} → Id x x
reflId = conid i1 refl

J-comp : ∀ {ℓ ℓ'} {A : Set ℓ} {x : A} {P : ∀ y → Id x y → Set ℓ'} →
         (d : P x reflId) → J P d reflId ≡ d
J-comp _ = refl

outPartial : ∀ {ℓ} {A : Set ℓ} → Partial i1 A → A
outPartial = λ f → f itIsOne

inPartial : ∀ {ℓ} {A : Set ℓ} → A → Partial i1 A
inPartial a = λ _ → a

module _ {ℓ ℓ'} {A : I → Set ℓ} {B : ∀ i → A i → Set ℓ'}
         (let ℓ = _ ; C : I → Set ℓ ; C i = (x : A i) → B i x) where
  compPi : (φ : I) → (u : ∀ i → Partial φ (C i)) → (a : C i0 [ φ ↦ u i0 ]) → C i1
  compPi φ u a' x1 = primComp
      (λ i → B i (v i)) (λ i o → u i o (v i)) (a (v i0)) where
    a = ouc a'
    v : (i : I) → A i
    v i = primTransp (λ j → A (i ∨ (~ j))) i x1
    f : ∀ i → (a : A i) → Partial φ (B i a)
    f i a = λ { (φ = i1) → u i itIsOne a  }


  compPi' : (φ : I) → (u : ∀ i → Partial φ (C i)) → (a : C i0 [ φ ↦ u i0 ]) → C i1
  compPi' φ u a = primComp C u (ouc a)

  test-compPi : (φ : I) → (u : ∀ i → Partial φ (C i)) → (a : C i0 [ φ ↦ u i0 ]) →
                  compPi φ u a ≡ compPi' φ u a
  test-compPi = λ φ u u0 → refl

module HCompPathP {ℓ} {A : I → Set ℓ} (u : A i0) (v : A i1) (φ : I)
         (let C = PathP A u v) (p : ∀ i → Partial φ C) (p0 : C [ φ ↦ p i0 ]) where

  hcompPathP : C
  hcompPathP j = primHComp (\ { i (φ = i1) → p i itIsOne j
                              ; i (j = i0) → u
                              ; i (j = i1) → v })
                           (ouc p0 j)


  test-hcompPathP : hcompPathP ≡ primHComp p (ouc p0)
  test-hcompPathP = refl

module TranspPathP {ℓ} {A : I → I → Set ℓ} (u : ∀ i → A i i0)(v : ∀ i → A i i1)
                  (let C = λ (i : I) → PathP (A i) (u i) (v i))
                  (p0 : C i0) where
 φ = i0
 transpPathP : C i1
 transpPathP j = primComp (λ i → A i j)
                          (\ { i (j = i0) → u i
                             ; i (j = i1) → v i })
                          (p0 j)

 test-compPathP : transpPathP ≡ primTransp C i0 p0
 test-compPathP = refl

module RecordComp where
  record R {ℓ ℓ'} (A : Set ℓ) (B : A → Set ℓ') (C : (x : A) → B x → Set ℓ)
     : Set (ℓ-max ℓ ℓ') where
   coinductive
   constructor _,_
   field
     fst : A
     snd : B fst
     trd : C fst snd
  open R

  hcompR : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'}
                   {C : (x : A) → B x → Set ℓ} →
    (let ℓ = _ ; Z : Set ℓ ; Z = R(A)(B)(C))
    (φ : I) → (u : ∀ i → Partial φ Z) → Z [ φ ↦ u i0 ] → Z
  fst (hcompR {A = A} {B} φ w w0)
    = primComp (\ _ → A) (λ i →  (λ{ (φ = i1) → fst (w i itIsOne) }) ) (fst (ouc w0))
  snd (hcompR {A = A} {B} φ w w0)
    = primComp (λ i → B (a i)) (λ i → (λ { (φ = i1) → snd (w i itIsOne) })) (snd (ouc w0))
    where
      a = fill (λ z → A) (λ i → (λ { (φ = i1) → fst (w i itIsOne) }) ) (inc (fst (ouc w0)))
  trd (hcompR {A = A} {B} {C} φ w w0)
    = primComp (λ i → C (a i) (b i)) ((λ i → (λ { (φ = i1) → trd (w i itIsOne)}))) (trd (ouc w0))
    where
      a = fill (λ z → A) (λ i → (λ { (φ = i1) → fst (w i itIsOne) }) ) (inc (fst (ouc w0)))
      b = fill (λ i → B (a i)) (λ i → (λ { (φ = i1) → snd (w i itIsOne) }) ) (inc (snd (ouc w0)))

  module _ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'}
                  {C : (x : A) → B x → Set ℓ}
                  (let ℓ = _ ; Z : Set ℓ ; Z = R(A)(B)(C))
                  (φ : I) (u : ∀ i → Partial φ (Z)) (a : Z [ φ ↦ u i0 ]) where
     test-compR-fst : hcompR {A = A} {B} {C} φ u a .fst ≡ primHComp u (ouc a) .fst
     test-compR-fst = refl

     test-compR-snd : hcompR {A = A} {B} {C} φ u a .snd ≡ primHComp u (ouc a) .snd
     test-compR-snd = refl

     test-compR-trd : hcompR {A = A} {B} {C} φ u a .trd ≡ primHComp u (ouc a) .trd
     test-compR-trd = refl



  module _ {ℓ ℓ'} {A : I → Set ℓ} {B : ∀ i → A i → Set ℓ'}
                   {C : ∀ i → (x : A i) → B i x → Set ℓ}
                   (let ℓ = _ ; Z : I → Set ℓ ; Z i = R(A i)(B i)(C i)) where

    φ = i0
    transpR : Z i0 → Z i1
    fst (transpR w0) =
      primTransp A φ (fst w0)
    snd (transpR w0) = primTransp (\ i → B i (a i)) φ (snd w0)
       where
         a = transpFill {A' = A i0} φ (λ i → inc (A i)) (fst w0)
    trd (transpR w0) = primTransp (\ i → C i (a i) (b i)) φ (trd w0)
       where
         a = transpFill {A' = A i0} φ (λ i → inc (A i)) (fst w0)
         b = transpFill {A' = B i0 (a i0)} φ (λ i → inc (B i (a i))) (snd w0)

  module _ {ℓ ℓ'} {A : I → Set ℓ} {B : ∀ i → A i → Set ℓ'}
                  {C : ∀ i → (x : A i) → B i x → Set ℓ}
                  (let ℓ = _ ; Z : I → Set ℓ ; Z i = R(A i)(B i)(C i))
                  (a : Z i0) where

    test-transpR-fst : fst (transpR {A = A} {B} {C} a) ≡ fst (primTransp Z i0 a)
    test-transpR-fst = refl

    test-transpR-snd : snd (transpR {A = A} {B} {C} a) ≡ snd (primTransp Z i0 a)
    test-transpR-snd = refl

    test-transpR-trd : trd (transpR {A = A} {B} {C} a) ≡ trd (primTransp Z i0 a)
    test-transpR-trd = refl


module _ {ℓ} {A : Set ℓ} {φ : I} {T : Partial φ (Set ℓ)}
             {e : PartialP φ (λ o → T o ≃ A)}
             where
  test-Glue-β : (t : PartialP φ T) (a : A [ φ ↦ (\ o → e o .fst (t o)) ]) →
    unglue {A = A} {φ = φ} {T = T} {e} (glue t (ouc a)) ≡ ouc a
  test-Glue-β _ _ = refl

  test-Glue-η : (b : Glue A T e) →
    (glue {φ = φ} (λ{ (φ = i1) → b }) (unglue {φ = φ} b)) ≡ b
  test-Glue-η b = refl

module _ {ℓ} {A : Set ℓ} (let φ = i1) {T : Partial φ (Set ℓ)}
             {e : PartialP φ (λ o → T o ≃ A)}
              where
  test-unglue-0 : (b : Glue A T e) →
    unglue {A = A} {φ = φ} {T = T} {e} b ≡ e itIsOne .fst b
  test-unglue-0 _ = refl

  test-unglue-2 : (t : PartialP φ T) (a : A [ φ ↦ (\ o → e o .fst (t o)) ]) →
    unglue {A = A} {φ = φ} {T = T} {e}
    (glue {A = A}{φ = φ}{T = T}{e} t (ouc a)) ≡ e itIsOne .fst (t itIsOne) -- = a
  test-unglue-2 _ _ = refl

  test-glue-0 : (t : PartialP φ T) (a : A [ φ ↦ (\ o → e o .fst (t o)) ]) →
    (glue {A = A} {T = T} {e} t (ouc a)) ≡ t itIsOne
  test-glue-0 _ _ = refl

eqToPath : ∀ {ℓ} {A B : Set ℓ} → A ≃ B → A ≡ B
eqToPath {ℓ} {A} {B} f = λ i → Glue B
  ([ ~ i ↦ (λ _ → A) , i ↦ (λ _ → B) ])
  ([ ~ i ↦ (λ{ (i = i0) → f }) , i ↦ (λ{ (i = i1) → pathToEquiv (λ _ → B) }) ])

univ = eqToPath

not : Bool → Bool
not true = false
not false = true

notnot : ∀ y → y ≡ not (not y)
notnot true = refl
notnot false = refl

nothelp : ∀ y (y₁ : Σ Bool \ x → (not x ≡ y)) → (not y , sym (notnot y)) ≡ y₁
nothelp y (true  , eq) = pathJ (λ y₁ eq' →
  (not y₁ , sym (notnot y₁)) ≡ (true  , eq')) refl _ eq
nothelp y (false , eq) = pathJ (λ y₁ eq' →
  (not y₁ , sym (notnot y₁)) ≡ (false , eq')) refl _ (eq)

notEquiv : Bool ≃ Bool
notEquiv = not , (λ { .equiv-proof y → (not y , sym (notnot y)) , nothelp y })

test : Bool
test = primComp (λ i → univ {A = Bool} {B = Bool} notEquiv i)
                {φ = i0} (λ _ → empty) true


test-test : test ≡ primComp (λ i → Bool) {φ = i0} (λ _ _ → false)
                  (primComp (λ i → Bool) {φ = i0} (λ _ _ → false)
                  (primComp (λ i → Bool) {φ = i0} (λ _ _ → false)
                  (primComp (λ i → Bool) {φ = i0} (λ _ _ → false)
                  (primComp (λ i → Bool) {φ = i0} (λ _ _ → false)
                  (primComp (λ i → Bool) {φ = i0} (λ _ _ → false)
                  (primComp (λ i → Bool) {φ = i0} (λ _ _ → false)
                  (primComp (λ i → Bool) {φ = i0} (λ _ _ → false)
                  (primComp (λ i → Bool) {φ = i0} (λ _ _ → false)
                   false))))))))
test-test = refl


test-test2 : test ≡ false
test-test2 = refl

test2 : Bool
test2 = primComp (λ i → eqToPath {A = Bool} {B = Bool} notEquiv i)
                 (λ _ → empty)
                 true


test2-test : test2 ≡ primComp (λ _ → Bool) {φ = i0} (λ _ _ → false)
                    (primComp (λ _ → Bool) {φ = i0} ((λ _ _ → false))
                    (primComp (λ _ → Bool) {φ = i0} ((λ _ _ → false))
                    (primComp (λ _ → Bool) {φ = i0} ((λ _ _ → false))
                     false)))
test2-test = refl

test3 : Bool
test3 = primComp (λ i → eqToPath {A = Bool} {B = Bool} notEquiv i)
                 (λ _ → empty)
                 true


test3-test : test3 ≡ primComp (λ i → Bool) {φ = i0} (λ _ _ → false)
                    (primComp (λ _ → Bool) {φ = i0} (λ _ _ → false)
                    (primComp (λ i → Bool) {φ = i0} (λ _ _ → false)
                     false))
test3-test = refl

data D2 (A : Set) : Set where
   c1 : D2 A
   c2 : D2 A

test5-test : ∀ j →  primComp (λ i → D2 Bool)
  (λ i → [ j ↦ (λ{ (j = i1) → c1 }) , ~ j ↦ (λ{ (j = i0) → c1 }) ]) c1 ≡ c1
test5-test j = refl

test6-test : (j : I → I) → primComp (λ i → D2 Bool) {φ = j i0} (λ i o → c1) c1 ≡ c1
test6-test j = refl

test4-test : ∀ j → primComp (λ i → Bool)
  (λ i → [ j ↦ (λ{ (j = i1) → false }) , ~ j ↦ (λ{ (j = i0) → false }) ] ) false ≡ false
test4-test j = refl


ListNot : List Bool ≡ List Bool
ListNot = λ i → List (univ {A = Bool} {B = Bool} notEquiv i)

trues : List Bool
trues = true ∷ true ∷ []

falses : List Bool
falses = primComp (λ i → ListNot i) (λ _ → empty) trues

test-falses : falses ≡ (false ∷ false ∷ [])
test-falses = refl

trues2 : List Bool
trues2 = primComp (λ i → trans ListNot ListNot i) (λ _ → empty) trues

test-trues2 : trues2 ≡ trues
test-trues2 = refl

trues3 : List Bool
trues3 = primComp (λ i → let p = trans ListNot ListNot in
                         trans p p i)
                  (λ _ → empty)
                  trues

test-trues3 : trues3 ≡ trues
test-trues3 = refl
