
open import Common.Prelude
open import Common.Reflect

{-# NO_TERMINATION_CHECK #-}
-- Note that in the body of the unquote, 'loops' really means 'quote loops'.
unquoteDecl loop =
  funDef (el (lit 0) (def (quote Nat) []))
         (clause [] (def loop []) ∷ [])
