-- Andreas, 2013-01-08, Reported by andres.sicard.ramirez, Jan 7
-- {-# OPTIONS -v term:10 -v term.matrices:40 #-}

-- The difference between @bar@ and @bar'@ is the position of the
-- hypothesis (n : ℕ). While @bar@ is accepted by the termination
-- checker, @bar'@ is rejected for it.

open import Common.Prelude renaming (Nat to ℕ)
open import Common.Product
open import Common.Coinduction
open import Common.Equality

data Foo : ℕ → Set where
  foo : (n : ℕ) → ∞ (Foo n) → Foo (suc n)

module NoWith where

  bar : (A : ℕ → Set) (n : ℕ) →
        ((m : ℕ) → A m → ∃ λ m' → m ≡ suc m' × A m') →
        A n → Foo n
  bar A n h An = subst Foo (sym (proj₁ (proj₂ (h n An))))
    (foo (proj₁ (h n An)) (♯ (bar A (proj₁ (h n An)) h (proj₂ (proj₂ (h n An))))))

module CorrectlyRejected where

  -- Proof rejected by the termination checker.
  --
  -- (If I do pattern matching on @n≡Sn'@, the proof is accepted.)
  bar' : (A : ℕ → Set) →
         ((m : ℕ) → A m → ∃ λ m' → m ≡ suc m' × A m') →
         (n : ℕ) → A n → Foo n
  bar' A h n An with h n An
  ... | (n' , n≡Sn' , An') = subst Foo (sym n≡Sn') (foo n' (♯ (bar' A h n' An')))

  postulate
    A : ℕ → Set
    h : (m : ℕ) → A m → ∃ λ m' → suc m' ≡ m × A m'

  -- Proof rejected by the termination checker.
  bar : (n : ℕ) → A n → Foo n
  bar n An with h n An
  ... | (n' , p , An') = subst Foo p (foo n' (♯ (bar n' An')))

module WasAccepted1 where

  -- Proof wrongly accepted by the termination checker.
  bar : (A : ℕ → Set) (n : ℕ) →
        ((m : ℕ) → A m → ∃ λ m' → m ≡ suc m' × A m') →
        A n → Foo n
  bar A n h An with h n An
  ... | (n' , n≡Sn' , An') = subst Foo (sym n≡Sn') (foo n' (♯ (bar A n' h An')))

-- Proof was wrongly accepted by the termination checker.

postulate
  A : ℕ → Set

H = (m : ℕ) → A m → ∃ λ m' → suc m' ≡ m × A m'

-- argument h was essential for faulty behavior

bar : (n : ℕ) → H → A n → Foo n
bar n h An with h n An
... | (n' , p , An') = subst Foo p (foo n' (♯ (bar n' h An')))

{- termination checking clause of bar
  lhs: 5 4 3 (_,_ 2 (_,_ 1 0))
  rhs: subst Foo p (foo n' (.Issue1014.♯-0 n h An n' p An'))
kept call from bar 5 4 3 (_,_ 2 (_,_ 1 0))
  to .Issue1014.♯-0 (n) (h) (An) (n') (p) (An')
  call matrix (with guardedness):
[[.,.,.,.,.]
,[.,0,.,.,.]
,[.,.,0,.,.]
,[.,.,.,0,.]
,[.,.,.,.,0]
,[.,.,.,.,0]
,[.,.,.,.,0]]
termination checking body of .Issue1014.♯-0
  : (n : ℕ)
    (h : (m : ℕ) → A m → Σ ℕ (λ m' → Σ (suc m' ≡ m) (λ x → A m')))
    (An : A n) (n' : ℕ) (p : suc n' ≡ n) (An' : A n') →
    ∞ (Foo n')
termination checking delayed clause of .Issue1014.♯-0
  lhs: 5 4 3 2 1 0
  rhs: ♯ bar n' h An'
kept call from .Issue1014.♯-0 5 4 3 2 1 0
  to bar (n') (h) (An')
  call matrix (with guardedness):
[[-1,.,.,.,.,.,.]
,[.,.,.,.,0,.,.]
,[.,.,0,.,.,.,.]
,[.,.,.,.,.,.,0]]
[Issue1014.bar] does termination check
-}

