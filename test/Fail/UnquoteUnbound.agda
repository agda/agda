module UnquoteUnbound where

open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Common.Reflection
open import Common.List

unquoteDecl foo = do
  nm ← freshName "a-fresh-name"
  defn ← getDefinition nm
  `def ← quoteTC defn >>= normalise
  typeError (termErr `def ∷ [])
