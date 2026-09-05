-- Smaller reproduction of the issue in #6198.
--
-- The preamble (a self-contained fragment of the cubical library) is
-- taken from test/Fail/Issue5838.agda.

{-# OPTIONS --safe --cubical #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Sigma

open import Agda.Primitive.Cubical
open import Agda.Primitive.Cubical public
  renaming ( primIMin       to _∧_  -- I → I → I
           ; primIMax       to _∨_  -- I → I → I
           ; primINeg       to ~_   -- I → I
           ; isOneEmpty     to empty
           ; primComp       to comp
           ; primHComp      to hcomp
           ; primTransp     to transp
           ; itIsOne        to 1=1 )

open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Cubical.Glue; open Helpers public
open import Agda.Builtin.Cubical.HCompU using ( prim^unglueU )
open import Agda.Builtin.Cubical.Sub public
  renaming ( primSubOut to outS
           )

---------------------------------------------------------------------------
-- Foundations

Type = Set

Path : (A : Type) → A → A → Type
Path A a b = PathP (λ _ → A) a b

isProp : Type → Type
isProp A = (x y : A) → x ≡ y

toPathP : {A : I → Type} {x : A i0} {y : A i1} → transp (λ i → A i) i0 x ≡ y → PathP A x y
toPathP {A = A} {x = x} p i =
  hcomp (λ j → λ { (i = i0) → x
                 ; (i = i1) → p j })
    (transp (λ j → A (i ∧ j)) (~ i) x)

isProp→PathP : ∀ {B : I → Type} → ((i : I) → isProp (B i))
               → (b0 : B i0) (b1 : B i1)
               → PathP (λ i → B i) b0 b1
isProp→PathP hB b0 b1 = toPathP (hB _ _ _)

---------------------------------------------------------------------------
-- Equivalence

-- The identity equivalence
idIsEquiv : (A : Type) → isEquiv (λ (x : A) → x)
idIsEquiv A .equiv-proof y =
  (y , refl) , λ z i → z .snd (~ i) , λ j → z .snd (~ i ∨ j)

idEquiv : (A : Type) → A ≃ A
idEquiv A .fst = λ x → x
idEquiv A .snd = idIsEquiv A

isPropIsEquiv : {A B : Type} (f : A → B) → isProp (isEquiv f)
isPropIsEquiv f p q i .equiv-proof y =
  let p2 = p .equiv-proof y .snd
      q2 = q .equiv-proof y .snd
  in p2 (q .equiv-proof y .fst) i
   , λ w j → hcomp (λ k → λ { (i = i0) → p2 w j
                            ; (i = i1) → q2 w (j ∨ ~ k)
                            ; (j = i0) → p2 (q2 w (~ k)) i
                            ; (j = i1) → w })
                   (p2 w (i ∨ j))

equivEq : {A B : Type} {e f : A ≃ B} → (h : e .fst ≡ f .fst) → e ≡ f
equivEq {e = e} {f = f} h i =
  h i , isProp→PathP (λ i → isPropIsEquiv (h i)) (e .snd) (f .snd) i

---------------------------------------------------------------------------
-- Univalence

Glue : (A : Type) {φ : I}
       → (Te : Partial φ (Σ Type λ T → T ≃ A))
       → Type
Glue A Te = primGlue A (λ x → Te x .fst) (λ x → Te x .snd)

unglue : {A : Type} (φ : I) {T : Partial φ Type}
         {e : PartialP φ (λ o → T o ≃ A)} → primGlue A T e → A
unglue φ = prim^unglue {φ = φ}

ua : ∀ {A B : Type} → A ≃ B → A ≡ B
ua {A = A} {B = B} e i = Glue B (λ { (i = i0) → (A , e)
                                   ; (i = i1) → (B , idEquiv B) })

---------------------------------------------------------------------------
-- Isomorphisms

record Iso (A B : Type) : Type where
  no-eta-equality
  constructor iso
  field
    fun : A → B
    inv : B → A
    rightInv : ∀ b → fun (inv b) ≡ b
    leftInv  : ∀ a → inv (fun a) ≡ a


-- Any iso is an equivalence
module _ {A B : Type} (i : Iso A B) where
  open Iso i renaming ( fun to f
                      ; inv to g
                      ; rightInv to s
                      ; leftInv to t)

  private
    module _ (y : B) (x0 x1 : A) (p0 : f x0 ≡ y) (p1 : f x1 ≡ y) where
      fill0 : I → I → A
      fill0 i = hfill (λ k → λ { (i = i1) → t x0 k
                               ; (i = i0) → g y })
                      (inS (g (p0 (~ i))))

      fill1 : I → I → A
      fill1 i = hfill (λ k → λ { (i = i1) → t x1 k
                               ; (i = i0) → g y })
                      (inS (g (p1 (~ i))))

      fill2 : I → I → A
      fill2 i = hfill (λ k → λ { (i = i1) → fill1 k i1
                               ; (i = i0) → fill0 k i1 })
                      (inS (g y))

      p : x0 ≡ x1
      p i = fill2 i i1

      sq : I → I → A
      sq i j = hcomp (λ k → λ { (i = i1) → fill1 j (~ k)
                              ; (i = i0) → fill0 j (~ k)
                              ; (j = i1) → t (fill2 i i1) (~ k)
                              ; (j = i0) → g y })
                     (fill2 i j)

      sq1 : I → I → B
      sq1 i j = hcomp (λ k → λ { (i = i1) → s (p1 (~ j)) k
                               ; (i = i0) → s (p0 (~ j)) k
                               ; (j = i1) → s (f (p i)) k
                               ; (j = i0) → s y k })
                      (f (sq i j))

      lemIso : (x0 , p0) ≡ (x1 , p1)
      lemIso i .fst = p i
      lemIso i .snd = λ j → sq1 i (~ j)

  isoToIsEquiv : isEquiv f
  isoToIsEquiv .equiv-proof y .fst .fst = g y
  isoToIsEquiv .equiv-proof y .fst .snd = s y
  isoToIsEquiv .equiv-proof y .snd z = lemIso y (g y) (fst z) (s y) (snd z)

  isoToEquiv : A ≃ B
  isoToEquiv .fst = _
  isoToEquiv .snd = isoToIsEquiv

---------------------------------------------------------------------------
-- Booleans

notEquiv : Bool ≃ Bool
notEquiv = isoToEquiv (iso not not notnot notnot)
  where
  not : Bool → Bool
  not true = false
  not false = true

  notnot : ∀ x → not (not x) ≡ x
  notnot true  = refl
  notnot false = refl

---------------------------------------------------------------------------
-- Circle

data S¹ : Type where
  base : S¹
  loop : base ≡ base

rotLoop : (a : S¹) → a ≡ a
rotLoop base       = loop
rotLoop (loop i) j =
  hcomp (λ k → λ { (i = i0) → loop (j ∨ ~ k)
                 ; (i = i1) → loop (j ∧ k)
                 ; (j = i0) → loop (i ∨ ~ k)
                 ; (j = i1) → loop (i ∧ k)}) base

DoubleCover : S¹ → Type
DoubleCover base     = Bool
DoubleCover (loop i) = ua notEquiv i

winding : Path S¹ base base → Bool
winding p = transp (λ i → DoubleCover (p i)) i0 false

---------------------------------------------------------------------------
-- The example showing the bug in
-- Agda.TypeChecking.Primitive.Cubical.Glue.

global : (i j : I) → Type
global i j = Glue S¹ λ
  { (i = i0) → S¹ , idEquiv S¹
  ; (i = i1) → S¹ , idEquiv S¹
  ; (j = i0) → S¹ , equivEq {e = idEquiv S¹} {f = idEquiv S¹} (λ k x → rotLoop x k) i
  ; (j = i1) → S¹ , idEquiv S¹
  }

T : (i m : I) → global i m
T i m = transp (λ j → global i (j ∧ m)) i0 base

E : (i m : I) → S¹
E i m = unglue (~ i ∨ i ∨ ~ m ∨ m) (T i m)

_ : winding (λ i → E i i0) ≡ true
_ = refl

_ : winding (λ i → E i i1) ≡ true
_ = refl

windingConst : (m : I) → winding (λ i → E i m) ≡ true
windingConst m = refl

---------------------------------------------------------------------------
-- Another example exercising the duplicated code in
-- Agda.TypeChecking.Primitive.Cubical.HCompU.

globalUSys : (i j : I) → I → Partial (~ i ∨ i ∨ ~ j ∨ j) Type
globalUSys i j k (i = i0) = S¹
globalUSys i j k (i = i1) = S¹
globalUSys i j k (j = i0) = S¹
globalUSys i j k (j = i1) = S¹

globalU : (i j : I) → Type
globalU i j = hcomp (globalUSys i j) (global i j)

TU : (i m : I) → globalU i m
TU i m = transp (λ j → globalU i (j ∧ m)) i0 base

EU : (i m : I) → S¹
EU i m =
  unglue (~ i ∨ i ∨ ~ m ∨ m)
    (prim^unglueU {φ = ~ i ∨ i ∨ ~ m ∨ m} {T = globalUSys i m} {A = inS (global i m)}
                  (TU i m))

_ : winding (λ i → EU i i0) ≡ true
_ = refl

_ : winding (λ i → EU i i1) ≡ true
_ = refl

windingConstU : (m : I) → winding (λ i → EU i m) ≡ true
windingConstU m = refl
