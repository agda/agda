-- Issue #1130, test generation of helper function

-- {-# OPTIONS -v tc.with:40 #-}

id : (A : Set) → A → A
id A = {!id′!}
 -- C-c C-h produces:       id′ : ∀ {A} → A
 -- when it should produce: id′ : ∀ {A} → A → A

f : (A : Set) (B : A → Set) (a : A) → B a
f A B a = {!g A a!}
  -- Before: ∀ {A} {B : A → Set} A₁ (a : A₁) → B a
  -- After:  ∀ A (a : A) {B : A → Set} → B a
  -- Andreas, 2019-10-12:  ∀ {A} {B : A → Set} (a : A) → B a

open import Agda.Builtin.Bool

if_then_else : ∀{a} {A : Set a} (b : Bool) (t e : A) → A
if true  then t else e = t
if false then t else e = e

-- Andreas, 2019-10-12, issue #1050: Prevent unnecessary normalization.

id₂ : (A B : Set) → if true then A else B → if false then B else A
id₂ A B x = {!id₂′ x!}
  -- C-c C-h produces
  -- id₂′ : ∀ {A} {B} (x : if true then A else B) →
  --        if false then B else A
