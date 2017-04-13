-- {-# OPTIONS -v 20 #-}
-- {-# OPTIONS -v tc.polarity:30 #-}
-- {-# OPTIONS -v tc.decl:30 #-}
-- {-# OPTIONS -v tc.term:30 #-}
-- {-# OPTIONS -v tc.conv.coerce:20 #-}
-- {-# OPTIONS -v tc.signature:30 #-}
-- {-# OPTIONS -v import.iface:100 #-}

module PrettyInterface where

open import Agda.Primitive
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

id : ∀{a} {A : Set a} → A → A
id {A = A} a = a

id2 : ∀{A : id Set} → id A → A
id2 x = x

plus0 : ∀ x → x + 0 ≡ x
plus0 zero = refl
plus0 (suc x) rewrite plus0 x = refl

Identity : ∀{a} {A : Set a} (f : A → A) → Set a
Identity f = ∀ x → f x ≡ x

plus-0 : Identity (_+ 0)
plus-0 = plus0

my-Fun : ∀{a b} (A : Set a) (F : A → Set b) → Set (a ⊔ b)
my-Fun A F = (x : A) → F x

syntax my-Fun A (λ x → B) = [ x ∷ A ]=> B

my-id : [ A ∷ Set ]=> [ x ∷ A ]=> A
my-id A x = x
