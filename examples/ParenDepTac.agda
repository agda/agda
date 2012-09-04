-- Author: Makoto Takeyama

module ParenDepTac where

----------------------------------------------------------------------
-- Preliminary
----------------------------------------------------------------------

infix 3  _≡_
data _≡_ {A : Set}(x : A) : A -> Set where
  refl : x ≡ x

subst : {A : Set}(C : A -> Set){x y : A} -> x ≡ y -> C y -> C x
subst C refl c = c

sym : {A : Set}{x y : A} -> x ≡ y -> y ≡ x
sym refl = refl

cong : {A B : Set}(f : A -> B){x y : A} -> x ≡ y -> f x ≡ f y
cong f refl = refl

infixl 2 _`tran`_
_`tran`_ : {A : Set}{x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
refl `tran` refl = refl

data FALSE : Set where
data TRUE  : Set where tt : TRUE

data Nat : Set where
  zer : Nat
  suc : Nat -> Nat

_+_ : Nat -> Nat -> Nat
zer   + n = n
suc m + n = suc ( m + n )

----------------------------------------------------------------------
-- Strings of parentheses
----------------------------------------------------------------------

infix 5 ≪_ ≫_
data Parens : Set where
  ε  : Parens
  ≪_ : Parens -> Parens
  ≫_ : Parens -> Parens

infixr 5 _·_

_·_ : Parens -> Parens -> Parens
ε    · ys = ys
≪ xs · ys = ≪ (xs · ys)
≫ xs · ys = ≫ (xs · ys)

·ass : (xs : Parens){ys zs : Parens} -> xs · (ys · zs) ≡ (xs · ys) · zs
·ass ε      = refl
·ass (≪ xs) = cong ≪_ (·ass xs)
·ass (≫ xs) = cong ≫_ (·ass xs)

·unitR : {xs : Parens} -> xs · ε ≡ xs
·unitR {ε}    = refl
·unitR {≪ xs} = cong ≪_ ·unitR
·unitR {≫ xs} = cong ≫_ ·unitR

_≫' : Parens -> Parens
xs ≫' = xs · ≫ ε
_≪' : Parens -> Parens
xs ≪' = xs · ≪ ε

----------------------------------------------------------------------
-- A poorman's tactics for equational reasoning
----------------------------------------------------------------------

infixr 5 _⊙_
data Exp : Set where
  Var : Nat    -> Exp
  Lit : Parens -> Exp
  _⊙_ : Exp -> Exp -> Exp

nf0 : Exp -> Exp -> Exp
nf0 (Var x)   e0 = Var x ⊙ e0
nf0 (Lit a)   e0 = Lit a ⊙ e0
nf0 (e1 ⊙ e2) e0 = nf0 e1 (nf0 e2 e0)

nf : Exp -> Exp
nf e = nf0 e (Lit ε)

Env = Nat -> Parens

module withEnv(ρ : Env) where

  ⟦_⟧ : Exp -> Parens
  ⟦ Var x   ⟧ = ρ x
  ⟦ Lit a   ⟧ = a
  ⟦ e1 ⊙ e2 ⟧ = ⟦ e1 ⟧ · ⟦ e2 ⟧

  nfSound0 : (e e0 : Exp) -> ⟦ e ⊙ e0 ⟧ ≡ ⟦ nf0 e e0 ⟧
  nfSound0 (Var x)   e0 = refl
  nfSound0 (Lit a)   e0 = refl
  nfSound0 (e1 ⊙ e2) e0 = sym (·ass ⟦ e1 ⟧) `tran`
                          cong (_·_ ⟦ e1 ⟧) (nfSound0 e2 e0)  `tran`
                          nfSound0 e1 (nf0 e2 e0)

  nfSound : (e : Exp) -> ⟦ e ⟧ ≡ ⟦ nf e ⟧
  nfSound e = sym ·unitR `tran` nfSound0 e (Lit ε)

  tac : (e1 e2 : Exp) -> nf e1 ≡ nf e2 -> ⟦ e1 ⟧ ≡ ⟦ e2 ⟧
  tac e1 e2 p = nfSound e1 `tran` subst (\x -> ⟦ x ⟧ ≡ ⟦ nf e2 ⟧) p refl `tran`
                sym (nfSound e2)

module tac4 (a0 a1 a2 a3 : Parens) where
  ρ : Env
  ρ zer                         = a0
  ρ (suc zer)                   = a1
  ρ (suc (suc zer))             = a2
  ρ (suc (suc (suc zer)))       = a3
  ρ (suc (suc (suc (suc _  )))) = ε
  open module tac4' = withEnv ρ public using (tac)

v0 = Var zer
v1 = Var (suc zer)
v2 = Var (suc (suc zer))
v3 = Var (suc (suc (suc zer)))
[≪] = Lit (≪ ε)
[≫] = Lit (≫ ε)

----------------------------------------------------------------------
-- Derivations of S and T grammars
--     indexed by their underlying strings
----------------------------------------------------------------------

infix  3 _∈S _∈T
infix  4 <_> _⟨_⟩
infixl 4 _•_

data  _∈S : Parens -> Set where
  εS  : ε ∈S
  <_> : {xs    : Parens} -> xs ∈S -> ≪ xs ≫' ∈S
  _•_ : {xs ys : Parens} -> xs ∈S -> ys ∈S -> xs · ys ∈S

data _∈T : Parens -> Set where
  εT   : ε ∈T
  _⟨_⟩ : {xs ys : Parens} -> xs ∈T -> ys ∈T -> xs · ≪ ys ≫' ∈T

----------------------------------------------------------------------
-- Equivalence of S and T grammars
----------------------------------------------------------------------

infixl 3 _○_
_○_ : {xs ys : Parens} -> xs ∈T -> ys ∈T -> xs · ys ∈T
t ○ εT                 = subst _∈T ·unitR    t
_○_ {xs} t (t1 ⟨ t2 ⟩) = subst _∈T (·ass xs) ((t ○ t1) ⟨ t2 ⟩)

S⊂T : {xs : Parens} -> xs ∈S -> xs ∈T
S⊂T εS        = εT
S⊂T (< s >)   = εT ⟨ S⊂T s ⟩
S⊂T (s1 • s2) = S⊂T s1 ○ S⊂T s2

T⊂S : {xs : Parens} -> xs ∈T -> xs ∈S
T⊂S εT          = εS
T⊂S (t1 ⟨ t2 ⟩) = T⊂S t1 • < T⊂S t2 >

----------------------------------------------------------------------
-- Recursively defined test function
----------------------------------------------------------------------

Test : Nat -> Parens -> Set
Test n       (≪ xs) = Test (suc n) xs
Test (suc n) (≫ xs) = Test n       xs
Test zer     (≫ xs) = FALSE
Test (suc n)  ε     = FALSE
Test zer      ε     = TRUE

----------------------------------------------------------------------
-- Soundness of Test
----------------------------------------------------------------------

lemTest : (m : Nat)(xs : Parens) -> Test m xs ->
          (n : Nat)(ys : Parens) -> Test n ys ->
          Test (m + n) (xs · ys)
lemTest m       (≪ xs) p  = lemTest (suc m) xs p
lemTest (suc m) (≫ xs) p  = lemTest m       xs p
lemTest zer     (≫ xs) ()
lemTest (suc m) ε      ()
lemTest zer     ε      tt = \ n ys q -> q

sound : {xs : Parens} -> xs ∈S -> Test zer xs
sound εS                  = tt
sound (<_>{xs} s)         = lemTest zer xs (sound s) (suc zer) (≫ ε) tt
sound (_•_{xs}{ys} s1 s2) = lemTest zer xs (sound s1) zer ys (sound s2)

----------------------------------------------------------------------
-- Completeness of Test
----------------------------------------------------------------------

complete : (xs : Parens) -> Test zer xs -> xs ∈S
complete xs0 p0 = parse init εS xs0 p0
  where
  data St : Nat -> Parens -> Set where
    init : St zer ε
    _*_≪ : {n  : Nat} ->
           {xs : Parens} -> St n xs ->
           {ys : Parens} -> ys ∈S   ->
           St (suc n) (xs · ys ≪')

  stPar : forall {n xs} -> St n xs -> Parens
  stPar {xs = xs} _ = xs

  ∈SPar : forall {xs} -> xs ∈S -> Parens
  ∈SPar {xs} _ = xs

  parse : {n  : Nat} ->
          {xs : Parens} -> St n xs   ->
          {ys : Parens} -> ys ∈S     ->
          (zs : Parens) -> Test n zs ->
          xs · ys · zs ∈S

  -- <SHIFT>  (st        ,  s ,  ≪ zs )  ↦  (st * s ≪ , εS         , zs)
  -- <REDUCE> (st * s3 ≪ ,  s ,  ≫ zs )  ↦  (st       , s3 • < s > , zs)
  -- <FINISH> (init      ,  s ,  ε    )  ↦  s

  parse {_} {xs} st {ys} s (≪ zs) p = subst _∈S eq (parse (st * s ≪) εS zs p)
    where open module foo = tac4 xs ys zs ε
          eq = tac (v0 ⊙ v1 ⊙ [≪]  ⊙ v2) ((v0 ⊙ v1 ⊙ [≪]) ⊙ v2) refl

  parse (st * s3 ≪) {ys} s (≫ zs) p
                                    = subst _∈S eq (parse st (s3 • < s >) zs p)
    where open module foo = tac4 (stPar st) (∈SPar s3) ys zs
          eq = tac ((v0 ⊙  v1 ⊙ [≪]) ⊙ v2 ⊙ [≫]  ⊙ v3)
                   ( v0 ⊙ (v1 ⊙ [≪]  ⊙ v2 ⊙ [≫]) ⊙ v3) refl

  parse ( _ * _ ≪) _ ε      ()

  parse init       _ (≫ zs) ()
  parse init       s ε      tt = subst _∈S ·unitR s

