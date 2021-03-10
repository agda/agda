
open import Agda.Builtin.Equality
open import Agda.Builtin.Reflection renaming (bindTC to _>>=_)
open import Agda.Builtin.String
open import Agda.Builtin.List
open import Agda.Builtin.Unit

impNames : Term → List String
impNames (pi (arg (arg-info hidden _) _) (abs x b)) = x ∷ impNames b
impNames _ = []

macro
  implicits : Name → Term → TC ⊤
  implicits x hole = do
    t ← getType x
    i ← quoteTC (impNames t)
    unify hole i

variable
  A : Set₁
  x : A

postulate
  f : (B : Set) → B ≡ B → Set

g : f _ x ≡ f _ x
g = refl

_ : implicits g ≡ "x.A.1" ∷ "x" ∷ []
_ = refl

postulate
  F : Set → Set₁
  P : {x : Set} → F x → Set
  Q : {x : Set₁} → x → Set
  p : P x
  q : Q x

_ : implicits p ≡ "x.A.1" ∷ "x" ∷ []
_ = refl

_ : implicits q ≡ "x.A" ∷ "x" ∷ []
_ = refl

fails : (A : Set) (f : F A) → P f
fails A f = p {x = f}
