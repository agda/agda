open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

postulate +-comm : ∀ m n → m + n ≡ n + m

-- Note that the following does not work because
-- p+q is not abstracted over in `+-comm p q` which means
-- Agda gets stuck trying to unify `p + q` and `q + p`

-- Cf. test/Succeed/UsingEq.agda

rew : ∀ m n p q → m + (p + q) + n ≡ m + (q + p) + n
rew m n p q with p+q ← p + q with refl ← +-comm p q = refl
