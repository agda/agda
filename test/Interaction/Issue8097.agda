open import Agda.Builtin.Equality

postulate
  A B : Set

to : A → B
to = {!!}

to-cong : ∀ {x y} → x ≡ y → to x ≡ to y
to-cong e = {!!} -- C-c C-a internal error
