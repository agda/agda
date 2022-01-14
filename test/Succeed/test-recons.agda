open import Agda.Builtin.Nat
open import Agda.Builtin.Unit
open import Agda.Builtin.Reflection renaming (bindTC to _>>=_)
open import Agda.Builtin.List
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality
open import Agda.Primitive

infix  0 case_of_
case_of_ : ∀ {a b}{A : Set a}{B : Set b} → A → (A → B) → B
case x of f = f x

map : ∀ {a b}{A : Set a}{B : Set b} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

reverse : ∀ {a}{A : Set a} → List A → List A
reverse {A = A} xs = reverseAcc xs []
  where
    reverseAcc : List A → List A → List A
    reverseAcc [] a = a
    reverseAcc (x ∷ xs) a = reverseAcc xs (x ∷ a)

data Maybe (X : Set) : Set where
  nothing : Maybe X
  just : X → Maybe X

data Fin : Nat → Set where
  zero : ∀ {n} → Fin (suc n)
  suc  : ∀ {n} → Fin n → Fin (suc n)

record RVec {a} (X : Set a) (n : Nat) : Set a where
  constructor vec
  field sel : Fin n → X

test-rvec : Nat → RVec Nat 5
test-rvec x = vec λ _ → x

get-len : Definition → TC Term
get-len (function (clause _ _ (con (quote vec)
                                  (_ ∷ _ ∷ (arg _ a) ∷ _)) ∷ [])) = quoteTC a
get-len _ = quoteTC "ERROR"

macro
  def-reg : Name → Term → TC ⊤
  def-reg n hole = do
    d ← getDefinition n
    l ← get-len d
    unify hole l

  def-recons : Name → Term → TC ⊤
  def-recons n hole = do
    d ← withReconstructed (getDefinition n)
    l ← get-len d
    unify hole l

  -- normaliseR perserves reconstructed expressions.
  def-normR : Name → Term → TC ⊤
  def-normR n hole = do
    (function (clause tel ps t ∷ [])) ←
      withReconstructed (getDefinition n)
      where _ → quoteTC "ERROR" >>= unify hole
    t ← inContext (reverse tel)
        (withReconstructed (normalise t))
    let d = function (clause tel ps t ∷ [])
    get-len d >>= unify hole

  -- normaliseR perserves reconstructed expressions.
  def-redR : Name → Term → TC ⊤
  def-redR n hole = do
    (function (clause tel ps t ∷ [])) ←
      withReconstructed (getDefinition n)
      where _ → quoteTC "ERROR" >>= unify hole
    t ← inContext (reverse tel) (withReconstructed (reduce t))
    let d = function (clause tel ps t ∷ [])
    get-len d >>= unify hole


test₁ : unknown ≡ def-reg test-rvec
test₁ = refl

test₂ : (lit (nat 5)) ≡ def-recons test-rvec
test₂ = refl

test₃ : (lit (nat 5)) ≡ def-normR test-rvec
test₃ = refl

test₄ : (lit (nat 5)) ≡ def-redR test-rvec
test₄ = refl


pictx : Term → Telescope
pictx (pi a (abs s x)) = (s , a) ∷ pictx x
pictx _ = []

macro
  get-ctx : Name → Term → TC ⊤
  get-ctx n hole = do
    t ← getType n
    let c = pictx t
    c ← withReconstructed
        (inContext (reverse c) getContext)
    quoteTC c >>= unify hole

bar : (A : Set) (eq : [] {A = A} ≡ []) (x : Nat) → ⊤
bar _ _ _ = tt

-- if getContext were to work incorrectly, this function wouldn't typecheck
test₅ : Telescope
test₅ = get-ctx bar


data NotAVec (X : Set) (y : Nat) : Set where
  mk : NotAVec X y

f : ∀ {n} → NotAVec Nat n → NotAVec Nat (suc n)
f mk = mk


macro
  chk-type : Term → TC ⊤
  chk-type hole = do
    T ← quoteTC (NotAVec Nat 5)
    t ← quoteTC (mk {X = Nat} {y = 5})
    (con _ (_ ∷ arg _ t ∷ [])) ← withReconstructed (checkType t T)
      where _ → quoteTC "ERROR" >>= unify hole
    quoteTC t >>= unify hole

-- checkType would leave unknown's without the call to withReconstructed
test₆ : chk-type ≡ lit (nat 5)
test₆ = refl


q : [] {A = Nat} ≡ [] {A = Nat}
q = refl

macro
  inf-type₁ : Term → TC ⊤
  inf-type₁ hole = do
    (function (clause _ _ b ∷ [])) ← withReconstructed (getDefinition (quote q))
      where _ → quoteTC "ERROR" >>= unify hole
    (def _ (l ∷ L ∷ e₁ ∷ e₂ ∷ [])) ← withReconstructed  (inferType b)
      where _ → quoteTC "ERROR" >>= unify hole
    (arg _ (con _ (_ ∷ (arg _ N) ∷ []))) ← returnTC e₁
      where _ → quoteTC "ERROR" >>= unify hole
    quoteTC N >>= unify hole

-- inferType would not reconstruct the arguments within the type
-- without the call to withReconstructed
test₇ : inf-type₁ ≡ def (quote Nat) []
test₇ = refl

-- A test case with a projection instead of a constructor.

r : RVec Nat 0
r .RVec.sel = λ _ → 2

eq : RVec.sel r ≡ λ _ → 2
eq = refl

macro
  inf-type₂ : Term → TC ⊤
  inf-type₂ hole = do
    (function (clause _ _ b ∷ [])) ← withReconstructed (getDefinition (quote eq))
      where _ → quoteTC "ERROR" >>= unify hole
    (def _ (_ ∷ _ ∷ arg _ lhs ∷ _ ∷ [])) ← withReconstructed  (inferType b)
      where _ → quoteTC "ERROR" >>= unify hole
    quoteTC lhs >>= unify hole

arg′ : {A : Set} → Visibility → Quantity → A → Arg A
arg′ v q = arg (arg-info v (modality relevant q))

test₈ :
  inf-type₂ ≡
  def (quote RVec.sel)
    (arg′ hidden  quantity-0 (def (quote lzero) []) ∷
     arg′ hidden  quantity-0 (def (quote Nat) []) ∷
     arg′ hidden  quantity-0 (lit (nat 0)) ∷
     arg′ visible quantity-ω (def (quote r) []) ∷
     [])
test₈ = refl
