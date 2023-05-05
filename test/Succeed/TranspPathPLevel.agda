{-# OPTIONS --cubical --show-implicit --no-double-check #-}
module TranspPathPLevel where
-- Double checker disabled because it does not know you can apply Paths
-- (it complains that _≡_ isn't a function type in the defn. of ex)

open import Agda.Primitive renaming (Set to Type)
open import Agda.Builtin.Cubical.Path
open import Agda.Primitive.Cubical
  renaming (primIMax to _∨_ ; primIMin to _∧_ ; primINeg to ~_ ; primComp to comp ; primHComp to hcomp ; primTransp to transp)

open import Agda.Builtin.Reflection hiding (Type)
open import Agda.Builtin.Unit
open import Agda.Builtin.List

postulate
  A : Type
  p : A ≡ A
  i : I

-- Bug: this should compute to something like hcomp (λ i → primPOr {lsuc lzero} ...) ...
--   previously, it computed to primPOr {λ _ → lsuc lzero} instead, which is wrong.
ex : Type
ex = transp {λ i → lsuc lzero} (λ i → A ≡ A) i0 p i

_>>=_ = bindTC

argN : ∀ {a} {A : Type a} → A → Arg A
argN = arg (arg-info visible (modality relevant quantity-ω))

u : ⊤
u = unquote λ m → do
  ex ← quoteTC ex

  -- Checking the reflected normal form of a Kan operation essentially
  -- always fails, since the normaliser freely assumes boundary
  -- conditions in the arguments to primPOr, but "users" (= abstract
  -- syntax) have to write (i = i0) patterns to get these.
  (def (quote hcomp) (l ∷ a ∷ phi ∷ arg _ tm ∷ _)) ← normalise ex
    where tm → typeError (strErr "test failed: transp in PathP applied did not evaluate to hcomp "∷ [])

  -- But we can check that the system given to hcomp checks at the type
  -- it should have, even if the hcomp wouldn't check:
  let ty = quoteTerm (I → Partial (i ∨ ~ i) Type)
  (lam _ _) ← checkType tm ty
    where _ → typeError (strErr "checking reduced hcomp system did not result in a lambda" ∷ [])

  unify m (quoteTerm tt)
