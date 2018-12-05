
open import Agda.Primitive
open import Agda.Builtin.Nat

-- Named implicit function types

postulate
  T : Set → Set → Set
  foo : {A = X : Set} {B : Set} → T X B
  bar : ∀ {A = X} {B} → T X B

foo₁ : (X : Set) → T X X
foo₁ X = foo {A = X} {B = X}

bar₁ : ∀ X → T X X
bar₁ X = bar {A = X} {B = X}

Id : {A = _ : Set} → Set
Id {A = X} = X

Id₁ : Set → Set
Id₁ X = Id {A = X}

-- With blanks

postulate
  namedUnused   : {A = _ : Set} → Set
  unnamedUsed   : {_ = X : Set} → X → X
  unnamedUnused : {_ = _ : Set} → Set

_ : Set
_ = namedUnused {A = Nat}

_ : Nat → Nat
_ = unnamedUsed {Nat} -- can't give by name

_ : Set
_ = unnamedUnused {Nat}

-- In left-hand sides

id : {A = X : Set} → X → X
id {A = Y} x = x

-- In with-functions

with-fun : ∀ {A} {B = X} → T A X → T A X
with-fun {A = A} {B = Z} x with T A Z
with-fun {B = Z} x | Goal = x

-- In datatypes

data List {ℓ = a} (A : Set a) : Set a where
  [] : List A
  _∷_ : A → List A → List A

List₁ = List {ℓ = lsuc lzero}

-- In module telescopes

module Named {A : Set} {B = X : Set} where
   postulate H : X → A

h : (A : Set) → A → A
h A = Named.H {A = A} {B = A}

postulate
  X : Set

open Named {A = X} {B = X}

hh : X → X
hh = H

-- Constructors

data Q (n : Nat) : Set where
  mkQ : Q n

data E {n = x} (q : Q x) : Set where
  mkE : E q

e₁ : (q : Q 1) → E q
e₁ q = mkE {n = 1} {q = q}

-- Generalized variables

variable
  m n : Nat

q₁ = mkQ {n = 1}

data D (x : Q n) : Q m → Set where
  refl : {y = z : Q m} → D x z

D₁  = D {n = 1}
D₁₂ = λ x → D {n = 1} x {m = 2}

refl′ = λ x → refl {n = 1} {x = x} {m = 2} {y = mkQ}
