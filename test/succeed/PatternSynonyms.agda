-- {-# OPTIONS -v scope.pat:10 #-}
-- {-# OPTIONS -v tc.lhs:10 #-}
module PatternSynonyms where


data ℕ : Set where
  zero : ℕ
  suc  : (n : ℕ) → ℕ

{-# BUILTIN NATURAL ℕ #-}
{-# BUILTIN ZERO zero #-}
{-# BUILTIN SUC suc #-}

pattern z    = zero
pattern sz   = suc z
pattern ss x = suc (suc x)

data _≡_ {A : Set}(x : A) : A → Set where
  refl : x ≡ x


test : z ≡ zero
test = refl

test′ : sz ≡ suc zero
test′ = refl

test″ : ss z ≡ suc (suc zero)
test″ = refl

test‴ : ss ≡ λ x → suc (suc x)
test‴ = refl

f : ℕ → ℕ
f z            = zero
f sz           = suc z
f (ss 0)       = 2
f (ss (suc n)) = n

test-f : f zero ≡ zero
test-f = refl

test-f′ : f (suc zero) ≡ suc zero
test-f′ = refl


test-f″ : f (suc (suc 0)) ≡ 2
test-f″ = refl

test-f‴ : ∀ {n} → f (suc (suc (suc n))) ≡ n
test-f‴ = refl

------------------------------------------------------------------------

data L (A : Set) : Set where
  nil  : L A
  cons : A → L A → L A

pattern cc x y xs = cons x (cons y xs)

test-cc : ∀ {A} → cc ≡ λ (x : A) y xs → cons x (cons y xs)
test-cc = refl

crazyLength : ∀ {A} → L A → ℕ
crazyLength nil          = 0
crazyLength (cons x nil) = 1
crazyLength (cc x y xs)  = 9000

swap : ∀ {A} → L A → L A
swap nil          = nil
swap (cons x nil) = cons x nil
swap (cc x y xs)  = cc y x xs

test-swap : ∀ {xs} → swap (cons 1 (cons 2 xs)) ≡ cons 2 (cons 1 xs)
test-swap = refl

------------------------------------------------------------------------
-- refl and _

record ⊤ : Set where
  constructor tt

data _⊎_ (A B : Set) : Set where
  inj₁ : (x : A) → A ⊎ B
  inj₂ : (y : B) → A ⊎ B

infixr 4 _,_
record Σ (A : Set)(B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ

_×_ : (A B : Set) → Set
A × B = Σ A λ _ → B

infixr 5 _+_
infixr 6 _*_

data Sig (O : Set) : Set₁ where
  ε ψ     : Sig O
  ρ       : (o : O) → Sig O
  ι       : (o : O) → Sig O
  _+_ _*_ : (Σ Σ′ : Sig O) → Sig O
  σ π     : (A : Set)(φ : A → Sig O) → Sig O


⟦_⟧ : ∀ {O} → Sig O → (Set → (O → Set) → (O → Set))
⟦ ε      ⟧ P R o = ⊤
⟦ ψ      ⟧ P R o = P
⟦ ρ o′   ⟧ P R o = R o′
⟦ ι o′   ⟧ P R o = o ≡ o′
⟦ Σ + Σ′ ⟧ P R o = ⟦ Σ ⟧ P R o ⊎ ⟦ Σ′ ⟧ P R o
⟦ Σ * Σ′ ⟧ P R o = ⟦ Σ ⟧ P R o × ⟦ Σ′ ⟧ P R o
⟦ σ A φ  ⟧ P R o = Σ A λ x → ⟦ φ x ⟧ P R o
⟦ π A φ  ⟧ P R o = (x : A) → ⟦ φ x ⟧ P R o


′List : Sig ⊤
′List = ε + ψ * ρ _

data μ {O}(Σ : Sig O)(P : Set)(o : O) : Set where
  ⟨_⟩ : ⟦ Σ ⟧ P (μ Σ P) o → μ Σ P o

List : Set → Set
List A = μ ′List A _

infixr 5 _∷_
pattern []       = ⟨ inj₁ _ ⟩
pattern _∷_ x xs = ⟨ inj₂ (x , xs) ⟩

length : ∀ {A} → List A → ℕ
length []       = zero
length (x ∷ xs) = suc (length xs)

test-list : List ℕ
test-list = 1 ∷ 2 ∷ []

test-length : length test-list ≡ 2
test-length = refl




′Vec : Sig ℕ
′Vec = ι 0
     + σ ℕ λ m → ψ * ρ m * ι (suc m)

Vec : Set → ℕ → Set
Vec A n = μ ′Vec A n

pattern []V     = ⟨ inj₁ refl ⟩
pattern _∷V_ x xs = ⟨ inj₂ (_ , x , xs , refl) ⟩

nilV : ∀ {A} → Vec A zero
nilV = []V

consV : ∀ {A n} → A → Vec A n → Vec A (suc n)
consV x xs = x ∷V xs

lengthV : ∀ {A n} → Vec A n → ℕ
lengthV []V       = 0
lengthV (x ∷V xs) = suc (lengthV xs)

test-lengthV : lengthV (consV 1 (consV 2 (consV 3 nilV))) ≡ 3
test-lengthV = refl

------------------------------------------------------------------------
-- .-patterns

pattern zr          = (.zero , refl)
pattern underscore² = _ , _

dot : (p : Σ ℕ λ n → n ≡ zero) → ⊤ × ⊤
dot zr = underscore²

------------------------------------------------------------------------
-- Implicit arguments

{-
pattern hiddenUnit = {_} -- XXX: We get lhs error msgs, can we refine
                         -- that?

imp : {p : ⊤} → ⊤
imp hiddenUnit = _
-}

data Box (A : Set) : Set where
  box : {x : A} → Box A

pattern [_] y = box {x = y}

b : Box ℕ
b = [ 1 ]

test-box : b ≡ box {x = 1}
test-box = refl


------------------------------------------------------------------------
-- Anonymous λs

g : ℕ → ℕ
g = λ { z → z
      ; sz → sz
      ; (ss n) → n
      }

test-g : g zero ≡ zero
test-g = refl

test-g′ : g sz ≡ suc zero
test-g′ = refl

test-g″ : ∀ {n} → g (suc (suc n)) ≡ n
test-g″ = refl

------------------------------------------------------------------------
-- λs

postulate
  X Y : Set
  h   : X → Y

p : (x : X)(y : Y) → h x ≡ y → ⊤
p x .((λ x → x) (h x)) refl = _

pattern app x = x , .((λ x → x) (h x))

p′ : (p : X × Y) → h (proj₁ p) ≡ proj₂ p → ⊤
p′ (app x) refl = _

------------------------------------------------------------------------
-- records

record Rec : Set where
  constructor rr
  field
    r : ℕ


rrr : (x : Rec) → x ≡ record { r = 0 } → ⊤
rrr .(record { r = 0}) refl = _

rrr′ : (x : Rec) → x ≡ record { r = 0 } → ⊤
rrr′ .(rr 0) refl = _

rrrr : (a : Rec × ℕ) → proj₁ a ≡ record { r = proj₂ a } → ⊤
rrrr (.(rr 0)       , 0)     refl = _
rrrr (.(rr (suc n)) , suc n) refl = _

pattern pair x = (.(record { r = x }) , x)

rrrr′ : (a : Rec × ℕ) → proj₁ a ≡ record { r = proj₂ a } → ⊤
rrrr′ (pair 0)       refl = _
rrrr′ (pair (suc n)) refl = _

------------------------------------------------------------------------
-- lets

pp : (x : X)(y : Y) → h x ≡ y → ⊤
pp x .(let i = (λ x → x) in i (h x)) refl = _

pattern llet x = x , .(let i = (λ x → x) in i (h x))

pp′ : (p : X × Y) → h (proj₁ p) ≡ proj₂ p → ⊤
pp′ (llet x) refl = _

------------------------------------------------------------------------
-- absurd patterns

pattern absurd = ()

data ⊥ : Set where

⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim absurd

------------------------------------------------------------------------
-- ambiguous constructors

data ℕ2 : Set where
  zero : ℕ2
  suc  : ℕ2 -> ℕ2

-- This needs a type signature, because it is ambiguous:
amb : ℕ2
amb = suc (suc zero)

-- This isn't ambiguous, because the overloading is resolved when the
-- pattern synonym is scope-checked:
unamb = ss z

------------------------------------------------------------------------
-- underscore

pattern trivial = ._

trivf : (a : ⊤) -> a ≡ tt -> ⊤
trivf trivial refl = trivial

------------------------------------------------------------------------
-- let open

pattern nuts = .(let open Σ in z)

foo : (n : ℕ) -> n ≡ z -> ℕ
foo nuts refl = nuts

------------------------------------------------------------------------
-- pattern synonym inside unparamterised module

module M where
  pattern sss x = suc (suc (suc x))

  a : ℕ
  a = sss 2

mb : ℕ
mb = M.sss 0

mf : ℕ -> ℕ -> ℕ
mf (M.sss _) = M.sss
mf _         = \ _ -> 0




{-
module M (A : Set)(a : A) where
  pattern peep x = x , .a

  pop : (z : A × A) -> proj₂ z ≡ a -> ⊤
  pop (peep x) refl = _

  peep' = peep


pop' : (z : ⊤ × ⊤) -> proj₂ z ≡ tt -> ⊤
pop' (M.peep tt) refl = _

peep' = M.peep
-}
