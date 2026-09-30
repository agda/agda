
open import Agda.Builtin.Equality

postulate
  foo : (A : Set) → A ≡ A

helper : {W : Set} (A : Set) → W → W ≡ A → (A → Set) → Set
helper A w refl f = f w

bar : (A : Set) → A → Set
bar A a = let A≡A = foo A in helper A a (foo A) {!!} -- A≡A : A ≡ A

baz : (A : Set) → A → Set
baz A a = let A≡A = foo A in helper A a (foo A) λ a' → {!!} -- A≡A : a ≡ a

f : (A : Set) → A → Set → Set
f A x = let y = x in λ B → {!!} -- y : x
