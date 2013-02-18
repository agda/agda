-- {-# OPTIONS -v tc.constr.findInScope:15 -v tc.meta.new:50 #-}
-- Andreas, 2012-10-20 issue raised by d.starosud
-- solved by dropping UnBlock constraints during trial candidate assignment
module Issue723 where

import Common.Level
open import Common.Prelude using (Bool; false; zero) renaming (Nat to ℕ)

record Default {ℓ} (A : Set ℓ) : Set ℓ where
  constructor create
  field default : A

open Default {{...}} using (default)

defBool : Default Bool
defBool = create false

defSet  : Default Set
defSet  = create Bool

defNat : Default ℕ
defNat = create zero

defDef : Default (Default ℕ)
defDef = create defNat

defFunc : ∀ {ℓ} {A : Set ℓ} → Default (A → A)
defFunc = create (λ x → x)

-- these lines are compiled successfully

id : ∀ {a} (A : Set a) → A → A
id A x = x

syntax id A x = x ∶ A

n₁ = default ∶ ℕ
f₁ = default ∶ (ℕ → ℕ)

-- WAS: but this one hangs on "Checking"
n₂ = default (5 ∶ ℕ) ∶ ℕ
-- n₂ = id ℕ (default (id ℕ 5))

n : ℕ
n = default 5
-- now we get unsolved metas
-- that's kind of ok

n₃ = (default ∶ (_ → _)) 5
-- also unsolved metas (worked before switching of the occurs-error (Issue 795))
