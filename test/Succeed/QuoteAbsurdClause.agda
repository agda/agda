
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Agda.Builtin.Sigma
open import Agda.Builtin.Reflection renaming (bindTC to _>>=_)

data ⊥ : Set where

[_] : {A : Set} → A → List A
[ x ] = x ∷ []

vArg : {A : Set} → A → Arg A
vArg x = arg (arg-info visible (modality relevant quantity-ω)) x

macro
  getFunDef : Name → Term → TC ⊤
  getFunDef f hole = do
    function cls ← getDefinition f
      where _ → error
    niceCls ← quoteTC cls
    unify hole niceCls

    where postulate error : _

noooo : (A : Set) → ⊥ → A
noooo A ()

-- Quoting the term `noooo Nat x` used to produce an absurd lambda
-- applied to `x`, which should not happen. It should instead simply
-- keep the term `noooo Nat x` as-is.
fooooo : ⊥ → Nat
fooooo x = noooo Nat x

test : getFunDef fooooo ≡
         [
           clause [ "x" , vArg (def (quote ⊥) []) ] [ vArg (var 0) ]
                  (def (quote noooo) (vArg (def (quote Nat) []) ∷ vArg (var 0 []) ∷ []))
         ]
test = refl
