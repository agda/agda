open import Agda.Builtin.Nat
open import Agda.Builtin.Unit
open import Agda.Builtin.Reflection renaming (bindTC to _>>=_)
open import Agda.Builtin.List
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality
open import Agda.Primitive

record X {a} (A : Set a) : Set a where
  field fld : A

d : X Nat
d = record { fld = 5 }

-- Here we test that suppressing reduction of lzero has no effect on the reconstruction
-- of parameters.  Essentially, we ignore ReduceDefs annotations when reconstructing
-- hidden parameters.
macro
  x : Term → TC ⊤
  x hole = do
      (function (clause tel ps t ∷ [])) ← withReconstructed (getDefinition (quote d))
        where _ → quoteTC "ERROR" >>= unify hole
      a ← withReconstructed (dontReduceDefs (quote lzero ∷ []) (normalise t))
      quoteTC a >>= unify hole

-- If we were to consider suppressed reduction of lzero, we end up with
-- Set ≠ Set lzero.
test₁ : Term
test₁ = x



map : ∀ {a b}{A : Set a}{B : Set b} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

reverse : ∀ {a}{A : Set a} → List A → List A
reverse {A = A} xs = reverseAcc xs []
  where
    reverseAcc : List A → List A → List A
    reverseAcc [] a = a
    reverseAcc (x ∷ xs) a = reverseAcc xs (x ∷ a)

foo : Nat → Nat
foo x = 1 + x

bar : Nat → Nat
bar x = foo (foo (x))

-- Here we test that normalisation respects ReduceDefs
-- when parameter reconstruction is on.
macro
  y : Term → TC ⊤
  y hole = do
      (function (clause tel ps t ∷ [])) ← withReconstructed (dontReduceDefs (quote foo ∷ []) (getDefinition (quote bar)))
        where _ → quoteTC "ERROR" >>= unify hole
      t ← inContext (reverse tel)
          (withReconstructed (dontReduceDefs (quote foo ∷ []) (normalise t)))
      quoteTC t >>= unify hole

test₂ : y ≡ def (quote foo) (arg _ (def (quote foo) _) ∷ [])
test₂ = refl
