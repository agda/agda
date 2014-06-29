
open import Common.Prelude
open import Common.Reflect

{-# NO_TERMINATION_CHECK #-}
unquoteDecl loop =
  funDef (el (lit 0) (def (quote Nat) []))
         (clause [] (def (quote loop) []) ∷ [])
