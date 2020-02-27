-- Andreas, 2018-06-12, issue #2170
-- Reported by tomjack

{-# OPTIONS --irrelevant-projections --subtyping #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Bool

infixr 42 _,_
record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ

record Irr (A : Set) : Set where
  constructor irr
  field
    .unirr : A
open Irr

-- Usually,  unirr (irr a) = .(a)  which is  DontCare a  in internal syntax.
-- The DontCare protection of an irrelevant field could be circumvented
-- using subtyping  irr : (.Bool → Irr Bool) ≤ (Bool → Irr Bool):
-- The argument  a  in  (i a)  would not have ArgInfo Irrelevant, even
-- after substitution irr/i.  Since the DontCare came from the ArgInfo of a,
-- there was none.  Now, the record constructor name also carries ArgInfo for
-- each of its fields, which is used to produce a DontCare.

bizarre : Irr (Σ (Bool → Irr Bool) (λ i → Σ (Irr Bool → Bool) (λ u → (a : Bool) → u (i a) ≡ a)))
bizarre = irr (irr , unirr , λ a → refl)  -- Should not pass

-- Expected error:
-- .(a) != a of type Bool
-- when checking that the expression refl has type .(a) ≡ a

-- The rest is proving False.

data ⊥ : Set where

¬_ : Set → Set
¬ A = (A → ⊥)

true≠false : ¬ (true ≡ false)
true≠false ()

infixr 30 _∙_
_∙_ : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl ∙ q = q

infix 42 !_
!_ : {A : Set} {x y : A} → x ≡ y → y ≡ x
! refl = refl

map-irr : {A B : Set} → (A → B) → Irr A → Irr B
map-irr f (irr x) = irr (f x)

factivity : ¬ (Irr ⊥)
factivity (irr ())

bad : Irr (true ≡ false)
bad = map-irr (λ { (i , u , s) → ! (s true) ∙ s false }) bizarre

boom : ⊥
boom = factivity (map-irr true≠false bad)


-- the hole here is is .(a) ≡ a
-- bizarre' : Irr (Σ (Irr Bool → Bool) (λ u → (a : Bool) → u (irr a) ≡ a))
-- bizarre' = irr (unirr , (λ a → {!!}))

-- also fails, unirr (irr a) = .(a)
-- bizarre' : Irr (Σ (Bool → Irr Bool) (λ i → Σ (Irr Bool → Bool) (λ u → (a : Bool) → u (i a) ≡ a)))
-- bizarre' = irr (irr , unirr , (λ a → refl {x = unirr (irr a)})
