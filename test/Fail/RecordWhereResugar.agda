
open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

record _×_ (A B : Set) : Set where
  field fst : A
        snd : B

open _×_

test : record { fst = 1; snd = 2}
     ≡ record where
         fst = 3
         snd = 4
test = refl
