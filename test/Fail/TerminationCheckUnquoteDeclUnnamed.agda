-- Check that unquoted functions are termination checked.
module _ where

open import Common.Prelude hiding (_>>=_)
open import Common.Reflection

`⊥ : Type
`⊥ = def (quote ⊥) []

data Box : Set where
  box : ⊥ → Box

unbox : Box → ⊥
unbox (box x) = x

`Box : Type
`Box = def (quote Box) []

{-
Generate
  aux : Box
  aux = box (unbox aux)
-}
makeLoop : TC ⊤
makeLoop =
  freshName "aux" >>= λ aux →
  declareDef (iArg aux) `Box >>= λ _ →
  defineFun aux (clause [] [] (con (quote box) (vArg (def (quote unbox) (vArg (def aux []) ∷ [])) ∷ [])) ∷ [])

unquoteDecl = makeLoop

it : ∀ {a} {A : Set a} {{_ : A}} → A
it {{x}} = x

-- loop : ⊥
-- loop = unbox it
