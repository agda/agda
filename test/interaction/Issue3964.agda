
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma

module _ {X : Set} {x : X} where

  test : (p q : Σ X (x ≡_)) → p ≡ q
  test (.x , refl) (z , q) = {!q!}

-- C-c C-c q RET:
-- WAS: test (_ , refl) (_ , refl)
-- WANT: preserved user-written pattern
--       test (.x , refl) (_ , refl)


  test' : (p q : Σ X (x ≡_)) → p ≡ q
  test' (x , refl) (z , q) = {!q!}

-- here it's fine!
-- C-c C-c q RET gives us:
-- test' (x , refl) (.x , refl) = {!!}
