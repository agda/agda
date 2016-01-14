
open import Common.Prelude
open import Common.Reflection
open import Common.TC

{-# NON_TERMINATING #-}
-- Note that in the body of the unquote, 'loop' really means 'quote loop'.
unquoteDecl loop =
  define loop (funDef (el (lit 0) (def (quote Nat) []))
                      (clause [] (def loop []) ∷ []))
