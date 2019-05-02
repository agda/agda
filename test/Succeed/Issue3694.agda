
import Agda.Builtin.Size

postulate
  F : (A : Set) (B : A → Set) → ((x : A) → B x) → Set

variable
  A : Set
  P : A → Set

postulate
  f : (r : (x : _) → P x) → F _ P (λ x → r x)
