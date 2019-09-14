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


data ⊥ : Set where
⊥-elim : ⊥ → {A : Set} → A
⊥-elim ()

¬odd0 : ∀ n → 0 ≡ 2 * n + 1 → ⊥
¬odd0 zero    ()
¬odd0 (suc n) ()

data Vec (A : Set) : Nat → Set where
  []  : Vec A 0
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

module _ {A : Set} where

  oddhead : ∀ {n} → Vec A (2 * n + 1) → A
  oddhead {n} xs
    -- here we cannot split on `xs` because Agda does not know
    -- whether `2 * n + 1` can unify with `0` or not

    -- A possible solution: abstract over p and then match on xs.
--      with p ← (2 * n + 1) | xs
--  ... | x ∷ _ = x
--  ... | []    = {!!}

    -- The problem however is that Agda insists we should consider
    -- two cases: `xs = []` and `xs = x ∷ _`. And in the `[]` branch
    -- we only know that:
    -- p  : Nat
    -- n  : Nat
    -- xs : Vec A 0
    -- If only we had somehow recorded that `p ← (2 * n + 1)` happened!
    -- This is what the inspect construct allows us to do.

    with eq .. p ← (2 * n + 1) | xs
  ... | x ∷ _ = x
  -- we can now use this equality proof to dismiss the impossible case.
  ... | []    = ⊥-elim (¬odd0 n eq)

  -- If you do not want to name the nat corresponding to `2 * n + 1`,
  -- you can use inspect together with an implicit with

  oddhead' : ∀ {n} → Vec A (2 * n + 1) → A
  oddhead' {n} xs with eq .. {2 * n + 1} | xs
  ... | x ∷ _ = x
  ... | []    = ⊥-elim (¬odd0 n eq)
