{-# OPTIONS --universe-polymorphism #-}
open import Common.Prelude
  renaming (Nat to ℕ; module Nat to ℕ)
   using (zero; suc; _+_; _∸_; List; []; _∷_; Bool; true; false)
open import Common.Level
open import Common.Reflection

module TermSplicing where

module Library where
  data Box {a} (A : Set a) : Set a where
    box : A → Box A

  record ⊤ : Set where
    constructor tt

  infixr 5 _×_
  record _×_ (A B : Set) : Set where
    constructor _,_
    field
      proj₁ : A
      proj₂ : B

  [_] : ∀ {A : Set} → A → List A
  [ x ] = x ∷ []

  replicate : ∀ {A : Set} → ℕ → A → List A
  replicate zero x = []
  replicate (suc n) x = x ∷ replicate n x

  foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
  foldr c n []       = n
  foldr c n (x ∷ xs) = c x (foldr c n xs)

  foldl : ∀ {A B : Set} → (A → B → A) → A → List B → A
  foldl c n []       = n
  foldl c n (x ∷ xs) = foldl c (c n x) xs

  reverse : ∀ {A : Set} → List A → List A
  reverse = foldl (λ rev x → x ∷ rev) []

  length : ∀ {A : Set} → List A → ℕ
  length = foldr (λ _ → suc) 0

  data Maybe (A : Set) : Set where
    nothing : Maybe A
    just    : A → Maybe A

  mapMaybe : ∀ {A B : Set} → (A → B) → Maybe A → Maybe B
  mapMaybe f (just x) = just (f x)
  mapMaybe f nothing  = nothing

  when : ∀ {A} → Bool → Maybe A → Maybe A
  when true  x = x
  when false _ = nothing

  infix 6 _≡_

  data _≡_ {a} {A : Set a} (x : A) : A -> Set where
    refl : x ≡ x

  _→⟨_⟩_ : ∀ (A : Set) (n : ℕ) (B : Set) → Set
  A →⟨ zero  ⟩ B = B
  A →⟨ suc n ⟩ B = A → A →⟨ n ⟩ B

open Library

module ReflectLibrary where
  lamᵛ : Term → Term
  lamᵛ t = lam visible (abs "_" t)

  lamʰ : Term → Term
  lamʰ t = lam hidden (abs "_" t)

  argᵛʳ : ∀{a} {A : Set a} → A → Arg A
  argᵛʳ = arg (argInfo visible relevant)

  argʰʳ : ∀{a} {A : Set a} → A → Arg A
  argʰʳ = arg (argInfo hidden relevant)

  app` : (Args → Term) → (hrs : List ArgInfo) → Term →⟨ length hrs ⟩ Term
  app` f = go [] where
    go : List (Arg Term) → (hrs : List ArgInfo) → Term →⟨ length hrs ⟩ Term
    go args []             = f (reverse args)
    go args (i ∷ hs) = λ t → go (arg i t ∷ args) hs

  con` : QName → (hrs : List ArgInfo) → Term →⟨ length hrs ⟩ Term
  con` x = app` (con x)

  def` : QName → (hrs : List ArgInfo) → Term →⟨ length hrs ⟩ Term
  def` x = app` (def x)

  var` : ℕ → (hrs : List ArgInfo) → Term →⟨ length hrs ⟩ Term
  var` x = app` (var x)

  coe : ∀ {A : Set} {z : A} n → (Term →⟨ length (replicate n z) ⟩ Term) → Term →⟨ n ⟩ Term
  coe zero    t = t
  coe (suc n) f = λ t → coe n (f t)

  con`ⁿʳ : QName → (n : ℕ) → Term →⟨ n ⟩ Term
  con`ⁿʳ x n = coe n (app` (con x) (replicate n (argInfo visible relevant)))

  def`ⁿʳ : QName → (n : ℕ) → Term →⟨ n ⟩ Term
  def`ⁿʳ x n = coe n (app` (def x) (replicate n (argInfo visible relevant)))

  var`ⁿʳ : ℕ → (n : ℕ) → Term →⟨ n ⟩ Term
  var`ⁿʳ x n = coe n (app` (var x) (replicate n (argInfo visible relevant)))

  sort₀ : Sort
  sort₀ = lit 0

  sort₁ : Sort
  sort₁ = lit 1

  `Set₀ : Term
  `Set₀ = sort sort₀

  unArg : ∀ {a} {A : Set a} → Arg A → A
  unArg (arg _ a) = a

  `Level : Term
  `Level = def (quote Level) []

  ℕ→Level : ℕ → Level
  ℕ→Level zero    = lzero
  ℕ→Level (suc n) = lsuc (ℕ→Level n)

  -- Can't match on Levels anymore
--   Level→ℕ : Level → ℕ
--   Level→ℕ zero    = zero
--   Level→ℕ (suc n) = suc (Level→ℕ n)

  setLevel : Level → Sort
  setLevel ℓ = lit 0 -- (Level→ℕ ℓ)

  _==_ : QName → QName → Bool
  _==_ = primQNameEquality

  decodeSort : Sort → Maybe Level
  decodeSort (set (con c [])) = when (quote lzero == c) (just lzero)
  decodeSort (set (con c (arg (argInfo visible relevant) s ∷ [])))
    = when (quote lsuc == c) (mapMaybe lsuc (decodeSort (set s)))
  decodeSort (set (sort s)) = decodeSort s
  decodeSort (set _) = nothing
  decodeSort (lit n) = just (ℕ→Level n)
  decodeSort unknown = nothing

  _`⊔`_ : Sort → Sort → Sort
  s₁ `⊔` s₂ with decodeSort s₁ | decodeSort s₂
  ...          | just n₁       | just n₂        = setLevel (n₁ ⊔ n₂)
  ...          | _             | _              = set (def (quote _⊔_) (argᵛʳ (sort s₁) ∷ argᵛʳ (sort s₂) ∷ []))

  Π : Arg Type → Type → Type
  Π t u = pi t (abs "_" u)

  Πᵛʳ : Type → Type → Type
  Πᵛʳ t u = Π (vArg t) u

  Πʰʳ : Type → Type → Type
  Πʰʳ t u = Π (hArg t) u

open ReflectLibrary

`ℕ : Term
`ℕ = def (quote ℕ) []

`ℕOk : (unquote (give `ℕ)) ≡ ℕ
`ℕOk = refl

idℕ : ℕ → ℕ
idℕ = unquote (give (lamᵛ (var 0 [])))

id : (A : Set) → A → A
id = unquote (give (lamᵛ (lamᵛ (var 0 []))))

idBox : Box ({A : Set} → A → A)
idBox = box (unquote (give (lamᵛ (var 0 []))))

-- builds a pair
_`,_ : Term → Term → Term
_`,_ = con`ⁿʳ (quote _,_) 2

`tt : Term
`tt = con (quote tt) []

tuple : List Term → Term
tuple = foldr _`,_ `tt

`refl : Term
`refl = con (quote refl) []

`zero : Term
`zero = con (quote ℕ.zero) []

`[] : Term
`[] = con (quote []) []

_`∷_ : (`x `xs : Term) → Term
_`∷_ = con`ⁿʳ (quote _∷_) 2

`abs : (`s `body : Term) → Term
`abs = con`ⁿʳ (quote abs) 2

`var : (`n `args : Term) → Term
`var = con`ⁿʳ (quote Term.var) 2

`lam : (`hiding `body : Term) → Term
`lam = con`ⁿʳ (quote lam) 2

`lit : Term → Term
`lit = con`ⁿʳ (quote Term.lit) 1

`string : Term → Term
`string = con`ⁿʳ (quote string) 1

`visible : Term
`visible = con (quote visible) []

`hidden : Term
`hidden = con (quote hidden) []

`[_`] : Term → Term
`[ x `] = x `∷ `[]

quotedTwice : Term
quotedTwice = `lam `visible (`abs (lit (string "_")) (`var `zero `[]))

unquoteTwice₂ : ℕ → ℕ
unquoteTwice₂ = unquote (give (unquote (give quotedTwice)))

unquoteTwice : ℕ → ℕ
unquoteTwice x = unquote (give (unquote (give (`var `zero `[]))))

id₂ : {A : Set} → A → A
id₂ = unquote (give (lamᵛ (var 0 [])))

id₃ : {A : Set} → A → A
id₃ x = unquote (give (var 0 []))

module Id {A : Set} (x : A) where
  x′ : A
  x′ = unquote (give (var 0 []))

k`ℕ : ℕ → Term
k`ℕ zero    = `ℕ
k`ℕ (suc n) = unquote (give (def (quote k`ℕ) [ argᵛʳ (var 0 []) ])) -- k`ℕ n

test : id ≡ (λ A (x : A) → x)
     × unquote (give `Set₀)                      ≡ Set
     × unquote (give `ℕ)                        ≡ ℕ
     × unquote (give (lamᵛ (var 0 [])))          ≡ (λ (x : Set) → x)
     × id                                        ≡ (λ A (x : A) → x)
     × unquote (give `tt)                        ≡ tt
     × (λ {A} → Id.x′ {A})                ≡ (λ {A : Set} (x : A) → x)
     × unquote (give (pi (vArg `Set₀) (abs "_" `Set₀)))  ≡ (Set → Set)
     × unquoteTwice                        ≡ (λ (x : ℕ) → x)
     × unquote (give (k`ℕ 42))                    ≡ ℕ
     × unquote (give (lit (nat 15)))              ≡ 15
     × unquote (give (lit (float 3.1415)))        ≡ 3.1415
     × unquote (give (lit (string "foo")))        ≡ "foo"
     × unquote (give (lit (char 'X')))            ≡ 'X'
     × unquote (give (lit (qname (quote ℕ))))      ≡ quote ℕ
     × ⊤
test = unquote (give (tuple (replicate n `refl))) where n = 15

Πⁿ : ℕ → Type → Type
Πⁿ zero    t = t
Πⁿ (suc n) t = Π (argʰʳ `Set₀) (Πⁿ n t)

ƛⁿ : Hiding → ℕ → Term → Term
ƛⁿ h zero    t = t
ƛⁿ h (suc n) t = lam h (abs "_" (ƛⁿ h n t))

-- projᵢ : Proj i n
-- projᵢ = proj i n
-- Projᵢ = {A₁ ... Ai ... An : Set} → A₁ → ... → Aᵢ → ... → An → Aᵢ
-- projᵢ = λ {A₁ ... Ai ... An} x₁ ... xᵢ ... xn → xᵢ

Proj : (i n : ℕ) → Term
Proj i n = Πⁿ n (go n) where
  n∸1 = n ∸ 1
  go : ℕ → Type
  go zero    = var ((n + n) ∸ i) []
  go (suc m) = Π (argᵛʳ (var n∸1 [])) (go m)

proj : (i n : ℕ) → Term
proj i n = ƛⁿ visible n (var (n ∸ i) [])

projFull : (i n : ℕ) → Term
projFull i n = ƛⁿ hidden n (proj i n)

ℕ→ℕ : Set
ℕ→ℕ = unquote (give (Π (argᵛʳ `ℕ) `ℕ))

ℕ→ℕOk : ℕ→ℕ ≡ (ℕ → ℕ)
ℕ→ℕOk = refl

``∀A→A : Type
``∀A→A = Πᵛʳ `Set₀ (var 0 [])

∀A→A : Set₁
∀A→A = unquote (give ``∀A→A)

Proj₁¹ : Set₁
Proj₁¹ = unquote (give (Proj 1 1))

Proj₁² : Set₁
Proj₁² = unquote (give (Proj 1 2))

Proj₂² : Set₁
Proj₂² = unquote (give (Proj 2 2))

proj₃⁵ : unquote (give (Proj 3 5))
proj₃⁵ _ _ x _ _ = x

proj₃⁵′ : Box (unquote (give (Proj 3 5)))
proj₃⁵′ = box (unquote (give (proj 3 5)))

proj₂⁷ : unquote (give (Proj 2 7))
proj₂⁷ = unquote (give (proj 2 7))

test-proj : proj₃⁵′                ≡ box (λ _ _ x _ _ → x)
          × Proj₁¹                 ≡ ({A : Set} → A → A)
          × Proj₁²                 ≡ ({A₁ A₂ : Set} → A₁ → A₂ → A₁)
          × Proj₂²                 ≡ ({A₁ A₂ : Set} → A₁ → A₂ → A₂)
          × unquote (give (Proj 3 5))     ≡ ({A₁ A₂ A₃ A₄ A₅ : Set} → A₁ → A₂ → A₃ → A₄ → A₅ → A₃)
          × unquote (give (projFull 1 1)) ≡ (λ {A : Set} (x : A) → x)
          × unquote (give (projFull 1 2)) ≡ (λ {A₁ A₂ : Set} (x₁ : A₁) (x₂ : A₂) → x₁)
          × unquote (give (projFull 2 2)) ≡ (λ {A₁ A₂ : Set} (x₁ : A₁) (x₂ : A₂) → x₂)
          × ∀A→A                   ≡ (∀ (A : Set) → A)
          × ⊤
test-proj = unquote (give (tuple (replicate n `refl))) where n = 9

module Test where
  data Squash (A : Set) : Set where
    squash : unquote (give (Π (arg (argInfo visible irrelevant) (var 0 []))
                              (def (quote Squash) (argᵛʳ (var 1 []) ∷ []))))

data Squash (A : Set) : Set where
  squash : .A → Squash A

`Squash : Term → Term
`Squash = def`ⁿʳ (quote Squash) 1

squash-type : Type
squash-type = Π (arg (argInfo visible irrelevant) (var 0 [])) (`Squash (var 1 []))

test-squash : ∀ {A} → (.A → Squash A) ≡ unquote (give squash-type)
test-squash = refl

`∀ℓ→Setℓ : Type
`∀ℓ→Setℓ = Πᵛʳ `Level (sort (set (var 0 [])))
