-- Andreas, 2018-11-23, issue #3304, report and test case by Nisse

open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma

map : {A B : Set} {P : A → Set} {Q : B → Set} →
      (f : A → B) → (∀ {x} → P x → Q (f x)) →
      Σ A P → Σ B Q
map f g (x , y) = (f x , g y)

postulate
  F         : Set → Set → Set
  apply     : {A B : Set} → F A B → A → B
  construct : {A B : Set} → (A → B) → F A B
  A         : Set
  B         : A → Set
  f         : A → A
  g         : ∀ {x} → B x → B (f x)

mutual

  k : Σ A B → Σ A _
  k = map f g

  h : F (Σ A B) (Σ A B)
  h = construct k

P : ∀ {x y} → k x ≡ k y → Set₁
P refl = Set

-- WAS: internal error in
-- TypeChecking.Rules.Term.catchIlltypedPatternBlockedOnMeta
--
-- EXPECTED:
-- I'm not sure if there should be a case for the constructor refl,
-- because I get stuck when trying to solve the following unification
-- problems (inferred index ≟ expected index):
--   k x ≟ k y
-- when checking that the pattern refl has type k x ≡ k y
