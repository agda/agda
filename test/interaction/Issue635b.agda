open import Common.Prelude renaming (Nat to ℕ; _+_ to _+ℕ_)
open import Common.Product
open import Common.Equality

postulate
  _≤ℕ_ : (n m : ℕ) → Set
  maxℕ : (n m : ℕ) → ℕ

When : (b : Bool) (P : Set) → Set
When true P = P
When false P = ⊤

infix 30 _⊕_
infix 20 _+_
infix 10 _≤_
infix 10 _<_

infixr 4 _,_

mutual

  data Cxt : Set where
    ∘   : Cxt
    _,_ : (Δ : Cxt) (b : Size Δ) → Cxt

  data Var : (Δ : Cxt) → Set where
    vz : ∀{Δ b}             → Var (Δ , b)
    vs : ∀{Δ b} (i : Var Δ) → Var (Δ , b)

  data Base (Δ : Cxt) : Set where
    zero : Base Δ
    ∞    : Base Δ
    var  : Var Δ → Base Δ

  record Size (Δ : Cxt) : Set where
    inductive
    constructor _⊕_
    field h : Base Δ
          n : ℕ

↑ : ∀{Δ} (a : Size Δ) → Size Δ
↑ (h ⊕ n) = h ⊕ suc n

_+_ : ∀{Δ} (a : Size Δ) (m : ℕ) → Size Δ
(h ⊕ n) + m = h ⊕ (n +ℕ m)

_-_ : ∀{Δ} (a : Size Δ) (m : ℕ) → Size Δ
(h ⊕ n) - m = h ⊕ (n ∸ m)

ClosedSize = Size ∘

data _≤_ : (a b : ClosedSize) → Set where
  leZZ : ∀{n m} (p : n ≤ℕ m) → zero ⊕ n ≤ zero ⊕ m
  leZ∞ : ∀{n m}               → zero ⊕ n ≤ ∞ ⊕ m
  le∞∞ : ∀{n m} (p : n ≤ℕ m) → ∞ ⊕ n ≤ ∞ ⊕ m

_<_ : (a b : ClosedSize) → Set
a < b = ↑ a ≤ b

max : (a b : ClosedSize) → ClosedSize
max (zero ⊕ n) (zero ⊕ n') = zero ⊕ maxℕ n n'
max (zero ⊕ n) (∞ ⊕ n') = ∞ ⊕ n'
max (zero ⊕ n) (var () ⊕ n')
max (∞ ⊕ n) (zero ⊕ n') = ∞ ⊕ n
max (∞ ⊕ n) (∞ ⊕ n') =  ∞ ⊕ maxℕ n n'
max (∞ ⊕ n) (var () ⊕ n')
max (var () ⊕ n)

-- Closed size valuation
mutual

  data Val (chk : Bool) : (Δ : Cxt) → Set where
    ∘    : Val chk ∘
    _,_<_∣_ : ∀{Δ} (ξ : Val chk Δ) (a : ClosedSize) b (p : When chk (a < eval ξ b)) → Val chk (Δ , b)

  lookup : ∀{Δ chk} (ξ : Val chk Δ) (x : Var Δ) → ClosedSize
  lookup (ξ , a < b ∣ p) vz     = a
  lookup (ξ , a < b ∣ p) (vs x) = lookup ξ x

  evalBase : ∀{Δ chk} (ξ : Val chk Δ) (a : Base Δ) → ClosedSize
  evalBase ξ zero    = zero ⊕ 0
  evalBase ξ ∞       = ∞ ⊕ 0
  evalBase ξ (var x) = lookup ξ x

  eval : ∀{Δ chk} (ξ : Val chk Δ) (a : Size Δ) → ClosedSize
  eval ξ (h ⊕ n) = evalBase ξ h + n

UVal = Val false  -- unsound valuation
SVal = Val true   -- sound valuation

update : ∀{Δ} (ρ : UVal Δ) (x : Var Δ) (f : ClosedSize → ClosedSize) → UVal Δ
update (ρ , a < b ∣ _) vz     f = ρ , f a < b ∣ _
update (ρ , a < b ∣ _) (vs x) f = update ρ x f , a < b ∣ _

data _≤V_ {chk chk'} : ∀ {Δ} (ρ : Val chk Δ) (ξ : Val chk' Δ) → Set where
  ∘   : ∘ ≤V ∘
  _,_ : ∀{Δ} {ρ : Val chk Δ} {ξ : Val chk' Δ} {a a' b p q}
        (r : ρ ≤V ξ) (s : a ≤ a') → (ρ , a < b ∣ p) ≤V (ξ , a' < b ∣ q)

lemma-str :  ∀ {Δ} (x : Var Δ) {n} {a} {ρ : UVal Δ} {ξ : SVal Δ}
  → (p : ρ ≤V ξ)
  → (q : a < lookup ξ x + n)
  → update ρ x (max (↑ a - n)) ≤V ξ
lemma-str vz     (p , s) q = {!q!}
lemma-str (vs x) (p , s) q = {!q!}
