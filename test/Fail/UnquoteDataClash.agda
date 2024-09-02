-- Andreas, 2024-04-14, re PR #5978
-- Trigger what used to be error "The name foo already has non-constructor definitions".
-- This error was introduced in PR #5978, but it could have been an ordinary ClashingDefinition error.

open import Agda.Builtin.Nat
open import Agda.Builtin.Unit
open import Agda.Builtin.Sigma
open import Agda.Builtin.Reflection
open import Common.Reflection
open import Common.List

[_] : ∀ {a} {A : Set a} → A → List A
[ x ] = x ∷ []

-- Copied from test/Succeed/UnquoteDeclData.
-- Does not really matter what we put here.

defineD : Name → Name → TC _
defineD D c =
  declareData D 1
    -- D (A : Set) : Nat → Set
    (pi (vArg (quoteTerm Set)) (abs ""
      (pi (vArg (quoteTerm Nat)) (abs ""
        (quoteTerm Set))))) >>= λ _ →
  defineData D
    -- c : (xs : List A) → D A (length xs)
    [(c , quantity-ω , pi (vArg (def (quote List) [ vArg (var 0 []) ])) (abs ""
            (def D (  vArg (var 1 [])
                    ∷ vArg (def (quote length) [ vArg (var 0 []) ])
                    ∷ [])))
    )]

module _ (foo : Name) where
  unquoteDecl data D constructor foo = defineD D foo

-- WAS:
-- The name foo already has non-constructor definitions
-- when scope checking the declaration
--   unquoteData D foo = defineD D foo
--
-- NOW:
-- Multiple definitions of foo. Previous definition at ...
-- when scope checking the declaration
--   unquoteData D foo = defineD D foo
