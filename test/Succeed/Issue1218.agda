
open import Common.Prelude
open import Common.Reflection

{-# NON_TERMINATING #-}
-- Note that in the body of the unquote, 'loop' really means 'quote loop'.
unquoteDecl loop =
  define (vArg loop)
         (funDef (def (quote Nat) [])
                 (clause [] [] (def loop []) ∷ []))
