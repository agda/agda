open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma

double : Nat → Set
double m = Σ Nat λ n → m ≡ n + n

-- 2*_ : Nat → Σ Nat double
-- 2*_ n with m ← n + n = m , n , {!!}
--  At this point we do not remember that m ≡ n + n and cannot
--  conclude the proof.

-- If only we could give a name to the proof that
-- `p ≡ e` after a `with p ← e` clause !

2*_ : Nat → Σ Nat double
2*_ n with eq .. m ← n + n = m , n , eq
