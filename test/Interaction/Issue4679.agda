-- Andreas, 2020-05-27 AIM XXXII, issue 4679
-- reported by Ayberk Tosun.

{-# OPTIONS --safe --cubical #-}

-- {-# OPTIONS -v tc.def.fun:10 #-}
-- {-# OPTIONS -v tc.cover.iapply:10 #-}

open import Agda.Primitive.Cubical renaming (primTransp to transp)
open import Agda.Builtin.Cubical.Path using (_≡_)

data ⊥ : Set where
data Unit : Set where
  tt : Unit

transport : {A B : Set} → A ≡ B → A → B
transport p a = transp (λ i → p i) i0 a

subst : ∀{A : Set} {x y : A} (B : A → Set) (p : x ≡ y) → B x → B y
subst B p pa = transport (λ i → B (p i)) pa

data Foo : Set where
  bar    : Unit → Foo
  baz    : Unit → Foo
  squash : (x y : Foo) → x ≡ y

bar≢baz : (x y : Unit) → bar x ≡ baz y → ⊥
bar≢baz tt tt p =
   subst {! λ { (bar _) → Unit ; (baz _) → ⊥ ; _ → ⊥ } !} p tt
   -- -- This function does not check:
   -- where
   -- P : Foo → Set
   -- P (bar _) = Unit
   -- P (baz _) = ⊥
   -- P _  = ⊥
   -- -- P p x != ⊥ of type Set
   -- -- when checking the definition of P

-- Giving the extended lambda should fail
-- since it fails boundary conditions (checkIApplyConfluence).
