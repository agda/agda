-- Possible improvements:
-- * Most of the code below is not reachable from main.
-- * The following primitives are not used at all: primPOr, primComp,
--   primHComp, prim^glueU and prim^unglueU.

{-# OPTIONS --erased-cubical #-}

-- The code from Agda.Builtin.Cubical.Glue should not be compiled.

open import Agda.Builtin.Cubical.Glue

open import Agda.Builtin.Cubical.HCompU
open import Agda.Builtin.Cubical.Id
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Cubical.Sub
open import Agda.Builtin.IO
open import Agda.Builtin.Nat
open import Agda.Builtin.String
open import Agda.Builtin.Unit
open import Agda.Primitive.Cubical

open import Erased-cubical-Cubical

postulate
  putStr : String → IO ⊤

{-# FOREIGN GHC import qualified Data.Text.IO #-}
{-# COMPILE GHC putStr = Data.Text.IO.putStr #-}
{-# COMPILE JS putStr =
    function (x) {
      return function(cb) {
        process.stdout.write(x); cb(0); }; } #-}

i₁ : I
i₁ = primIMax (primIMax (primINeg i0) i1) (primIMin i1 i0)

i₁-1 : IsOne i₁
i₁-1 = IsOne1 (primIMax (primINeg i0) i1) (primIMin i1 i0)
         (IsOne2 (primINeg i0) i1 itIsOne)

p₁ : Partial i1 Nat
p₁ = λ _ → 12

p₂ : PartialP i1 (λ _ → Nat)
p₂ = λ _ → 12

p₃ : PartialP i0 (λ _ → Nat)
p₃ = isOneEmpty

subst :
  ∀ {a p} {A : Set a}
  (P : A → Set p) (f : I → A) → P (f i0) → P (f i1)
subst P eq p = primTransp (λ i → P (eq i)) i0 p

p₄ : 12 ≡ 12
p₄ = λ _ → 12

n₁ : Nat
n₁ = p₄ i0

s : Sub Nat i1 (λ _ → 13)
s = inc 13

n₂ : Nat
n₂ = primSubOut s

i₂ : I
i₂ = primFaceForall (λ _ → i1)

i₃ : Id 12 12
i₃ = conid i0 p₄

i₄ : I
i₄ = primDepIMin i1 (λ _ → i0)

i₅ : I
i₅ = primIdFace i₃

p₅ : 12 ≡ 12
p₅ = primIdPath i₃

n₃ : Nat
n₃ = primIdJ (λ _ _ → Nat) 14 i₃

n₄ : Nat
n₄ = primIdElim (λ _ _ → Nat) (λ _ _ _ → 14) i₃

Is-proposition : Set → Set
Is-proposition A = (x y : A) → x ≡ y

data ∥_∥ (A : Set) : Set where
  ∣_∣        : A → ∥ A ∥
  @0 trivial : Is-proposition ∥ A ∥

rec : {A B : Set} → @0 Is-proposition B → (A → B) → ∥ A ∥ → B
rec p f ∣ x ∣           = f x
rec p f (trivial x y i) = p (rec p f x) (rec p f y) i

main : IO ⊤
main =
  putStr (rec easy
            (λ where
               true  → "Success\n"
               false → "Failure\n")
            ∣ true ∣)

-- It should be possible to mention things that are not compiled in
-- type signatures.

u₁ : Not-compiled → ⊤
u₁ _ = tt

@0 A : Set₁
A = Set

u₂ : A → ⊤
u₂ _ = tt
