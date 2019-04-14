
open import Agda.Primitive

postulate
  F : (a : Level) → Set a → Set a
  P : (a : Level) (A : Set a) → F a A → Set a
  p : (a : Level) (A : Set a) (x : F a A) → P a A x
  Q : (a : Level) (A : Set a) → A → Set a

variable
  a : Level
  A : Set a

postulate
  q : (x : F _ A) → Q a _ (p a A x)

q' : {a : Level} {A : Set a} (x : F a A) → Q a (P a A x) (p a A x)
q' {a} {A} = q {a} {A}
