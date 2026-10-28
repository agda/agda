-- Andreas, 2026-10-19, AIM XLIII issue #8847
-- Test case and report by Satoshi
-- 'instance' was silently ignored by 'unquoteDecl'.
-- Now it triggers a UselessInstance warning (under the usual condition
-- that no "instanceable" declaration is in the instance block).

module Issue8847 where

open import Agda.Builtin.Reflection renaming (bindTC to _>>=_; returnTC to pure)
open import Agda.Builtin.List
open import Agda.Builtin.Unit

--------------------------------------------------------------------------------

pattern vArg x = arg (arg-info visible   (modality relevant quantity-ω)) x
pattern iArg x = arg (arg-info instance′ (modality relevant quantity-ω)) x

makeAlias : Name → Term → TC ⊤
makeAlias alias original = do
  _ ← declareDef (vArg alias) unknown
  defineFun alias (clause [] [] original ∷ [])

makeInstanceAlias : Name → Term → TC ⊤
makeInstanceAlias alias original = do
  _ ← declareDef (iArg alias) unknown
  defineFun alias (clause [] [] original ∷ [])

--------------------------------------------------------------------------------

it : {A : Set} → ⦃ A ⦄ → A
it ⦃ x ⦄ = x

data Unit : Set where
  unit : Unit

module Ok where

  private
    unquoteDecl unit-alias = makeInstanceAlias unit-alias (quoteTerm unit)

  _ : Unit
  _ = it


module NotOk where

  private instance
    unquoteDecl unit-alias = makeAlias unit-alias (quoteTerm unit)

  -- Error: No instance of type Unit was found in scope when checking that the expression it has type Unit
  _ : Unit
  _ = it
