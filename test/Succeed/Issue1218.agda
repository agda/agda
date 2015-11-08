
open import Common.Prelude
open import Common.Reflection

{-# NON_TERMINATING #-}
-- Note that in the body of the unquote, 'loops' really means 'quote loops'.
unquoteDecl loop =
  funDef (el (lit 0) (def (quote Nat) []))
         (clause [] (def loop []) ∷ [])
