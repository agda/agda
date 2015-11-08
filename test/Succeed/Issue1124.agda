-- Andreas, 2014-05-08
-- Reported by guillaume.brunerie, Yesterday

{-# OPTIONS --show-implicit #-}
-- {-# OPTIONS -v tc.cc:25 -v reduce.compiled:95 #-}
-- {-# OPTIONS --show-implicit -v tc.inj:30 -v tc.conv:20 -v tc.meta.assign:10 #-}

-- The code below gives the following odd error:

-- > Incomplete pattern matching when applying Cubical._.C

-- The definition of [C] by pattern matching does not seem incomplete, but even if it were, it should be detected when type checking [C], not when using it (!).
-- The last definition [test] is the one triggering the error, if you comment it then everything typechecks.

record Unit : Set where
  constructor unit

data _==_ {i} {A : Set i} (a : A) : A → Set where
  idp : a == a

data Nat : Set where
  O : Nat
  S : Nat → Nat

record BS (B : Set) (C : B → Set) : Set where
  constructor bs
  field
    {b₁ b₂} : B
    c₁ : C b₁
    c₂ : C b₂
    p : b₁ == b₂

postulate A : Set

B : Nat → Set
C : (n : Nat) → B n → Set

B O = Unit
B (S n) = BS (B n) (C n)

-- No bug if no match on unit
-- C O _ = A
C O unit = A
C (S n) (bs {b₁} c₁ c₂ idp) = _==_ {A = _} c₁ c₂

-- Due to a bug in TypeChecking.Patterns.Match
-- a failed match of (C n b) against (C O unit)
-- turned into (C n unit).
-- This was because all patterns were matched in
-- parallel, and evaluations of successfull matches
-- (and a record constructor like unit can always
-- be successfully matched) were returned, leading
-- to a reassembly of (C n b) as (C n unit) which is
-- illtyped.

-- Now patterns are matched left to right and
-- upon failure, no further matching is performed.

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B
open _×_ public

PathOver : {A : Set} (B : A → Set)
  {x y : A} (p : x == y) (u : B x) (v : B y) → Set
PathOver B idp u v = (u == v)

syntax PathOver B p u v =
  u == v [ B ↓ p ]

pair×= : {A B : Set} {a a' : A} (p : a == a') {b b' : B} (q : b == b') → (a , b) == (a' , b')
pair×= idp idp = idp

bs= : {B : Set} {C : B → Set}
      {b₁ b₁' : B} {pb₁ : b₁ == b₁'}
      {b₂ b₂' : B} {pb₂ : b₂ == b₂'}
      {c₁ : C b₁} {c₁' : C b₁'} (pc₁ : c₁ == c₁' [ C ↓ pb₁ ])
      {c₂ : C b₂} {c₂' : C b₂'} (pc₂ : c₂ == c₂' [ C ↓ pb₂ ])
      {p : b₁ == b₂} {p' : b₁' == b₂'} (α : p == p' [ (λ u → fst u == snd u) ↓ pair×= pb₁ pb₂ ])
      → bs c₁ c₂ p == bs c₁' c₂' p'
bs= {pb₁ = idp} {pb₂ = idp} idp idp idp = idp

_=□^[_]_ : {a b c d : A} (p : a == b) (qr : (a == c) × (b == d)) (s : c == d) → Set
p =□^[ qr ] s = C (S (S O)) (bs {b₁ = bs _ _ idp} p s (bs= {pb₁ = idp} {pb₂ = idp} (fst qr) (snd qr) idp))

test : {a b : A} (p q : a == b) → (p =□^[ idp , idp ] q) == (p == q)
test p q = idp

{-
compareTerm (C n unit) =< (?0 n {b₁} c₁ c₂) : Set
term (?0 n {b₁} c₁ c₂) :>= (C n unit)
term (?0 n {b₁} c₁ c₂) :>= (C n unit)
solving _111 := (λ n {b₁} c₁ c₂ → C n unit)
-}
