open import Agda.Builtin.Nat

data Tree : Set where
  `    : Nat → Tree
  _`+_ : Tree → Tree → Tree

⟦_⟧ : Tree → Nat
⟦ ` n    ⟧ = n
⟦ t `+ u ⟧ = ⟦ t ⟧ + ⟦ u ⟧

data Target : Tree → Set where
  0+_ : ∀ e → Target (` 0 `+ e)
  _+0 : ∀ e → Target (e `+ ` 0)
  [_] : ∀ e → Target e

target : ∀ e → Target e
target (` 0 `+ e) = 0+ e
target (e `+ ` 0) = e +0
target e          = [ e ]

optimise   : Tree → Tree
structural : Tree → Tree

optimise t with {structural t} | target (structural t)
... | 0+ e  = e
... | e +0  = e
... | [ e ] = e

structural (` n)    = ` n
structural (e `+ f) = optimise e `+ optimise f

open import Agda.Builtin.Equality

suc-cong : ∀ {m n} → m ≡ n → suc m ≡ suc n
suc-cong refl = refl

+-cong : ∀ {m n p q} → m ≡ n → p ≡ q → m + p ≡ n + q
+-cong refl refl = refl

trans : {m n p : Nat} → m ≡ n → n ≡ p → m ≡ p
trans refl eq = eq

m≡m+0 : ∀ m → m ≡ m + 0
m≡m+0 0       = refl
m≡m+0 (suc m) = suc-cong (m≡m+0 m)

optimise-sound   : ∀ t → ⟦ optimise t ⟧ ≡ ⟦ t ⟧
structural-sound : ∀ t → ⟦ structural t ⟧ ≡ ⟦ t ⟧

optimise-sound t with {structural t} | target (structural t) | structural-sound t
... | 0+ e  | eq = eq
... | e +0  | eq = trans (m≡m+0 ⟦ e ⟧) eq
... | [ e ] | eq = eq

structural-sound (` n)    = refl
structural-sound (e `+ f) = +-cong (optimise-sound e) (optimise-sound f)
