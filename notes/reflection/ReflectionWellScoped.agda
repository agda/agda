-- {-# OPTIONS --cubical-compatible --safe --no-sized-types --no-guardedness #-}
-- Well-scoped de Bruijn indices in reflection

-- module Agda.Builtin.ReflectionWellScope where

module ReflectionWellScoped where

open import Agda.Primitive
open import Agda.Builtin.Bool
open import Agda.Builtin.Char
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Erase
open import Agda.Builtin.Float
open import Agda.Builtin.Int
open import Agda.Builtin.List
open import Agda.Builtin.Maybe
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma
open import Agda.Builtin.String
open import Agda.Builtin.Unit
open import Agda.Builtin.Word
import Agda.Builtin.Reflection as R
open R public using
 ( Name
 ; primQNameEquality
 ; primQNameLess
 ; primShowQName
 ; Associativity
 ; left-assoc
 ; right-assoc
 ; non-assoc
 ; Precedence
 ; related
 ; unrelated
 ; Fixity
 ; fixity
 ; primQNameFixity
 ; primQNameToWord64s
 ; Meta
 ; primMetaEquality
 ; primMetaLess
 ; primShowMeta
 ; primMetaToNat
 ; Visibility
 ; visible
 ; hidden
 ; instance′
 ; Relevance
 ; relevant
 ; irrelevant
 ; Quantity
 ; quantity-0
 ; quantity-ω
 ; Modality
 ; modality
 ; ArgInfo
 ; arg-info
 ; Arg
 ; arg
 ; Literal
 ; nat
 ; word64
 ; float
 ; char
 ; string
 ; name
 ; meta
 )

-- Standard definitions missing from the builtin modules

private
  _×_ : ∀{ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set _
  A × B = Σ A λ _ → B
  variable
    A B : Set

  trustMe : ∀ {a} {A : Set a} {x y : A} → x ≡ y
  trustMe = primEraseEquality prf where postulate prf : _

  length : ∀{ℓ} {A : Set ℓ} → List A → Nat
  length [] = 0
  length (_ ∷ xs) = 1 + length xs

  map : (A → B) → List A → List B
  map f [] = []
  map f (x ∷ xs) = f x ∷ map f xs

  infixr 10 _++_
  _++_ : List A → List A → List A
  [] ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  reverse : List A → List A
  reverse {A} = go [] module Reverse where
    go : List A → List A → List A
    go acc [] = acc
    go acc (x ∷ xs) = go (x ∷ acc) xs

  -- We do traversals in the Maybe Applicative.

  module MaybeBind where
    _>>=_ : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
    just x >>= k = k x
    nothing >>= k = nothing

  infixl 4 _<$>_

  _<$>_ : {A B : Set} → (A → B) → Maybe A → Maybe B
  f <$> just x = just (f x)
  f <$> nothing = nothing

  infixl 4 _<*>_

  _<*>_ : {A B : Set} → Maybe (A → B) → Maybe A → Maybe B
  nothing <*> ma = nothing
  just f  <*> ma = f <$> ma

  traverseDeco : {C : Set} → (A → Maybe B) → C × A → Maybe (C × B)
  traverseDeco f (c , a) = (c ,_) <$> f a

  traverseList : (A → Maybe B) → List A → Maybe (List B)
  traverseList f [] = just []
  traverseList f (x ∷ xs) = _∷_ <$> f x <*> traverseList f xs

  -- Deciding Nat equality

  SemidecidableEq : Set → Set
  SemidecidableEq A = (x y : A) → Maybe (x ≡ y)

  cong : {A B : Set} (f : A → B) {a b : A} → a ≡ b → f a ≡ f b
  cong f refl = refl

  subst : {A : Set} (P : A → Set) {a b : A} → a ≡ b → P a → P b
  subst P refl px = px

  subst₂ : {A B : Set} (P : A → B → Set) {a b : A} {x y : B} →
           a ≡ b → x ≡ y → P a x → P b y
  subst₂ P refl refl px = px

  _≟_ : SemidecidableEq Nat
  zero ≟ zero = just refl
  suc m ≟ zero = nothing
  zero ≟ suc n = nothing
  suc m ≟ suc n = cong suc <$> m ≟ n

  -- can't be bothered to prove this
  length-reverse : (xs : List A) → length (reverse xs) ≡ length xs
  length-reverse xs = trustMe


-- Well-scoped de Bruijn indices version of Agda.Builtin.Reflection
------------------------------------------------------------------------

-- Name abstraction --

private
  variable
    n m : Nat

data Abs {a} (A : Nat → Set a) (n : Nat) : Set a where
  abs : (s : String) (x : A (suc n)) → Abs A n

-- {-# BUILTIN ABS    Abs #-}
-- {-# BUILTIN ABSABS abs #-}

-- Variables --

data Var : Nat → Set where
  zero : Var (suc n)
  suc  : (x : Var n) → Var (suc n)

data Tele (A : Nat → Set) (n : Nat) : Nat → Set where
  emptyTel : Tele A n zero
  extTel   : A n → Tele A (suc n) m → Tele A n (suc m)

-- Terms and patterns --

data Term (n : Nat) : Set
data Sort (n : Nat) : Set
data Pattern (n m : Nat) : Set
data Clause (n : Nat) : Set
Type = Term

Telescope : (n m : Nat) → Set
Telescope = Tele (λ k → String × Arg (Type k))

data Term n where
  var       : (x : Var n) (args : List (Arg (Term n))) → Term n
  con       : (c : Name) (args : List (Arg (Term n))) → Term n
  def       : (f : Name) (args : List (Arg (Term n))) → Term n
  lam       : (v : Visibility) (t : Abs Term n) → Term n
  pat-lam   : (cs : List (Clause n)) (args : List (Arg (Term n))) → Term n
    -- Function defined by cs stuck on args.
  pi        : (a : Arg (Type n)) (b : Abs Type n) → Term n
  agda-sort : (s : Sort n) → Term n
  lit       : (l : Literal) → Term n
  meta      : (x : Meta) → List (Arg (Term n)) → Term n
  unknown   : Term n

data Sort n where
  set     : (t : Term n) → Sort n  -- E.g. Set ℓ
  lit     : (m : Nat) → Sort n     -- E.g. Set₁
  prop    : (t : Term n) → Sort n  -- E.g. Prop ℓ
  propLit : (m : Nat) → Sort n     -- E.g. Prop₁
  inf     : (m : Nat) → Sort n     -- E.g. Setω₅
  unknown : Sort n

-- We don't track linearity of pattern variables here.
-- We don't track arity of constructors either yet.
data Pattern n m where
  con    : (c : Name) (ps : List (Arg (Pattern n m))) → Pattern n m
  dot    : (t : Term (n + m))  → Pattern n m
  var    : (x : Var m)     → Pattern n m
  lit    : (l : Literal) → Pattern n m
  proj   : (f : Name)    → Pattern n m  -- only at the top-level
  absurd : (x : Var m)     → Pattern n m  -- absurd patterns counts as variables

Patterns = λ n m → List (Arg (Pattern n m))

data Clause n where
  clause        : (tel : Telescope n m) (ps : List (Arg (Pattern n m))) (t : Term (n + m)) → Clause n
  absurd-clause : (tel : Telescope n m) (ps : List (Arg (Pattern n m))) → Clause n

-- {-# BUILTIN AGDATERM      Term    #-}
-- {-# BUILTIN AGDASORT      Sort    #-}
-- {-# BUILTIN AGDAPATTERN   Pattern #-}
-- {-# BUILTIN AGDACLAUSE    Clause  #-}

-- {-# BUILTIN AGDATERMVAR         var       #-}
-- {-# BUILTIN AGDATERMCON         con       #-}
-- {-# BUILTIN AGDATERMDEF         def       #-}
-- {-# BUILTIN AGDATERMMETA        meta      #-}
-- {-# BUILTIN AGDATERMLAM         lam       #-}
-- {-# BUILTIN AGDATERMEXTLAM      pat-lam   #-}
-- {-# BUILTIN AGDATERMPI          pi        #-}
-- {-# BUILTIN AGDATERMSORT        agda-sort #-}
-- {-# BUILTIN AGDATERMLIT         lit       #-}
-- {-# BUILTIN AGDATERMUNSUPPORTED unknown   #-}

-- {-# BUILTIN AGDASORTSET         set     #-}
-- {-# BUILTIN AGDASORTLIT         lit     #-}
-- {-# BUILTIN AGDASORTPROP        prop    #-}
-- {-# BUILTIN AGDASORTPROPLIT     propLit #-}
-- {-# BUILTIN AGDASORTINF         inf     #-}
-- {-# BUILTIN AGDASORTUNSUPPORTED unknown #-}

-- {-# BUILTIN AGDAPATCON    con     #-}
-- {-# BUILTIN AGDAPATDOT    dot     #-}
-- {-# BUILTIN AGDAPATVAR    var     #-}
-- {-# BUILTIN AGDAPATLIT    lit     #-}
-- {-# BUILTIN AGDAPATPROJ   proj    #-}
-- {-# BUILTIN AGDAPATABSURD absurd  #-}

-- {-# BUILTIN AGDACLAUSECLAUSE clause        #-}
-- {-# BUILTIN AGDACLAUSEABSURD absurd-clause #-}

mapArg : (A → B) → Arg A → Arg B
mapArg f (arg i x) = arg i (f x)

unscopeAbs : ∀{A : Nat → Set} → (∀ {n} → A n → B) → Abs A n → R.Abs B
unscopeAbs f (abs s x) = R.abs s (f x)

unscopeVar : Var n → Nat
unscopeVar zero = zero
unscopeVar (suc x) = suc (unscopeVar x)

{-# TERMINATING #-}
unscopeTerm : Term n → R.Term
unscopeArgs : List (Arg (Term n)) → List (Arg R.Term)
unscopeArgs = map (mapArg unscopeTerm)

unscopeSort : Sort n → R.Sort
unscopeClause : Clause n → R.Clause

unscopeTerm (var x args) = R.var (unscopeVar x) (unscopeArgs args)
unscopeTerm (con c args) = R.con c (unscopeArgs args)
unscopeTerm (def f args) = R.def f (unscopeArgs args)
unscopeTerm (lam v t) = R.lam v (unscopeAbs unscopeTerm t)
unscopeTerm (pat-lam cs args) = R.pat-lam (map unscopeClause cs) (unscopeArgs args)
unscopeTerm (pi a b) = R.pi (mapArg unscopeTerm a) (unscopeAbs unscopeTerm b)
unscopeTerm (agda-sort s) = R.agda-sort (unscopeSort s)
unscopeTerm (lit l) = R.lit l
unscopeTerm (meta x args) = meta x (unscopeArgs args)
unscopeTerm unknown = R.unknown

unscopeSort (set t) = R.set (unscopeTerm t)
unscopeSort (lit m) = R.lit m
unscopeSort (prop t) = R.prop (unscopeTerm t)
unscopeSort (propLit m) = R.propLit m
unscopeSort (inf m) = R.inf m
unscopeSort unknown = R.unknown

unscopeTelescope : Telescope n m → R.Telescope
unscopeTele : {T : Nat → Set} {R : Set} →
              (∀ {m} → T m → R) → Tele T n m → List R

unscopePattern : Pattern n m → R.Pattern
unscopePatterns : Patterns n m → List (Arg R.Pattern)
unscopePatterns = map (mapArg unscopePattern)

unscopeClause (clause tel ps t) = R.clause (unscopeTelescope tel) (unscopePatterns ps) (unscopeTerm t)
unscopeClause (absurd-clause tel ps) = R.absurd-clause (unscopeTelescope tel) (unscopePatterns ps)

unscopeTelescope = unscopeTele λ { (s , arg i t) → (s , arg i (unscopeTerm t)) }

unscopeTele f emptyTel = []
unscopeTele f (extTel t tel) = f t ∷ unscopeTele f tel

unscopePattern (con c ps) = R.con c (unscopePatterns ps)
unscopePattern (dot t) = R.dot (unscopeTerm t)
unscopePattern (var x) = R.var (unscopeVar x)
unscopePattern (lit l) = R.lit l
unscopePattern (proj f) = R.proj f
unscopePattern (absurd x) = R.absurd (unscopeVar x)

ScopeCheck : (A : Set) (B : Nat → Set) → Set
ScopeCheck A B = {n : Nat} (a : A) → Maybe (B n)

ScopeCheckDep : (A : Set) (B : Nat → A → Set) → Set
ScopeCheckDep A B = {n : Nat} (a : A) → Maybe (B n a)

traverseArg : (A → Maybe B) → Arg A → Maybe (Arg B)
traverseArg f (arg i x) = arg i <$> f x

-- traverseArg : (∀ n → A n → Maybe (B n)) → Abs A n → Maybe (Abs B n)

scopeCheckAbs : {B : Nat → Set} → ScopeCheck A B → ScopeCheck (R.Abs A) (Abs B)
scopeCheckAbs f (R.abs s x) = abs s <$> f x

scopeCheckVar : ScopeCheck Nat Var
scopeCheckVar {n = zero} _ = nothing
scopeCheckVar {n = suc n} zero = just zero
scopeCheckVar {n = suc n} (suc i) = suc <$> scopeCheckVar i

{-# TERMINATING #-}
scopeCheckTerm : ScopeCheck R.Term Term

scopeCheckType : ScopeCheck R.Type Type
scopeCheckType = scopeCheckTerm

scopeCheckArgs : ScopeCheck (List (Arg R.Term)) (λ n → List (Arg (Term n)))
scopeCheckArgs = traverseList (traverseArg scopeCheckTerm)

scopeCheckSort : ScopeCheck R.Sort Sort
scopeCheckClause : ScopeCheck R.Clause Clause

scopeCheckTerm (R.var x args) = var <$> scopeCheckVar x <*> scopeCheckArgs args
scopeCheckTerm (R.con c args) = con c <$> scopeCheckArgs args
scopeCheckTerm (R.def f args) = def f <$> scopeCheckArgs args
scopeCheckTerm (R.lam v t) = lam v <$> scopeCheckAbs scopeCheckTerm t
scopeCheckTerm (R.pat-lam cs args) = pat-lam <$> traverseList scopeCheckClause cs <*> scopeCheckArgs args
scopeCheckTerm (R.pi a b) = pi <$> traverseArg scopeCheckType a <*> scopeCheckAbs scopeCheckType b
scopeCheckTerm (R.agda-sort s) = agda-sort <$> scopeCheckSort s
scopeCheckTerm (R.lit l) = just (lit l)
scopeCheckTerm (meta x args) = meta x <$> scopeCheckArgs args
scopeCheckTerm R.unknown = just unknown

scopeCheckSort (R.set t) = set <$> scopeCheckTerm t
scopeCheckSort (R.lit n) = just (lit n)
scopeCheckSort (R.prop t) = prop <$> scopeCheckTerm t
scopeCheckSort (R.propLit n) = just (propLit n)
scopeCheckSort (R.inf n) = just (inf n)
scopeCheckSort R.unknown = just unknown

scopeCheckTele : {B : Nat → Set} → ScopeCheck A B → ScopeCheckDep (List A) (λ n xs → Tele B n (length xs))
-- scopeCheckTele : {B : Nat → Set}
--   → ScopeCheck A B → {n : Nat} (xs : List A) → Maybe (Tele B n (length xs))
scopeCheckTele f [] = just emptyTel
scopeCheckTele f (x ∷ xs) = extTel <$> f x <*> scopeCheckTele f xs

scopeCheckTelescope : ScopeCheckDep (List (String × Arg R.Type)) (λ n xs → Telescope n (length xs))
scopeCheckTelescope args with length args | length-reverse args
... | _ | refl = scopeCheckTele (traverseDeco (traverseArg scopeCheckType)) (reverse args)

scopeCheckPattern : {m : Nat} → ScopeCheck R.Pattern (λ n → Pattern n m)
scopeCheckPatterns : {m : Nat} → ScopeCheck (List (Arg R.Pattern)) (λ n → Patterns n m)
scopeCheckPatterns = traverseList (traverseArg scopeCheckPattern)

scopeCheckPattern (R.con c ps) = con c <$> scopeCheckPatterns ps
scopeCheckPattern (R.dot t) = dot <$> scopeCheckTerm t
scopeCheckPattern (R.var x) = var <$> scopeCheckVar x
scopeCheckPattern (R.lit l) = just (lit l)
scopeCheckPattern (R.proj f) = just (proj f)
scopeCheckPattern (R.absurd x) = absurd <$> scopeCheckVar x

scopeCheckClause (R.clause tel ps t) = clause <$> scopeCheckTelescope tel <*> scopeCheckPatterns ps <*> scopeCheckTerm t
scopeCheckClause (R.absurd-clause tel ps) = absurd-clause <$> scopeCheckTelescope tel <*> scopeCheckPatterns ps


data Thin : (m, n : Nat) → Set where
  done : Thin 0 0
  skip : Thin m n → Thin m (suc n)
  keep : Thin m n → Thin (suc m) (suc n)

ones : Thin m m
ones {zero} = done
ones {suc m} = keep ones

none : Thin 0 m
none {zero} = done
none {suc m} = skip none

_<>_ : ∀ {p q} → Thin m n → Thin p q → Thin (m + p) (n + q)
done    <> ph = ph
skip th <> ph = skip (th <> ph)
keep th <> ph = keep (th <> ph)

Strengthenable : (Nat → Set) → Set
Strengthenable T = ∀ {m n} → Thin m n → T n → Maybe (T m)

strengthenVar : Strengthenable Var
strengthenVar done k = just k
strengthenVar (skip th) zero = nothing
strengthenVar (skip th) (suc k) = strengthenVar th k
strengthenVar (keep th) zero = just zero
strengthenVar (keep th) (suc v) = suc <$> strengthenVar th v

strengthenAbs : ∀ {T} → Strengthenable T →
                Strengthenable (Abs T)
strengthenAbs f th (abs s x) = abs s <$> f (keep th) x

{-# TERMINATING #-}
strengthenType      : Strengthenable Type
strengthenTerm      : Strengthenable Term
strengthenSort      : Strengthenable Sort
strengthenArg       : Strengthenable (λ n → Arg (Term n))
strengthenArgs      : Strengthenable (λ n → List (Arg (Term n)))
strengthenClause    : Strengthenable Clause
strengthenClauses   : Strengthenable (λ n → List (Clause n))
strengthenTele      : ∀ {T} → Strengthenable T → Strengthenable (λ n → Tele T n m)
strengthenTelescope : Strengthenable (λ n → Telescope n m)
strengthenPattern   : Strengthenable (λ n → Pattern n m)
strengthenPatterns  : Strengthenable (λ n → Patterns n m)

strengthenSort th (set t) = set <$> strengthenTerm th t
strengthenSort th (lit l) = just (lit l)
strengthenSort th (prop t) = prop <$> strengthenTerm th t
strengthenSort th (propLit l) = just (propLit l)
strengthenSort th (inf m) = just (inf m)
strengthenSort th unknown = just unknown

strengthenArg th = traverseArg (strengthenTerm th)

strengthenArgs th = traverseList (strengthenArg th)

strengthenTerm th (var v args) = var <$> strengthenVar th v <*> strengthenArgs th args
strengthenTerm th (con c args) = con c <$> strengthenArgs th args
strengthenTerm th (def f args) = def f <$> strengthenArgs th args
strengthenTerm th (lam v t) = lam v <$> strengthenAbs strengthenTerm th t
strengthenTerm th (pat-lam cs args) = pat-lam <$> strengthenClauses th cs <*> strengthenArgs th args
strengthenTerm th (pi a b) = pi <$> strengthenArg th a <*> strengthenAbs strengthenTerm th b
strengthenTerm th (agda-sort s) = agda-sort <$> strengthenSort th s
strengthenTerm th (lit l) = just (lit l)
strengthenTerm th (meta m args) = meta m <$> strengthenArgs th args
strengthenTerm th unknown = just unknown

strengthenType = strengthenTerm

strengthenClause th (clause tel ps t) =
  clause <$> strengthenTelescope th tel <*> strengthenPatterns th ps <*> strengthenTerm (th <> ones) t
strengthenClause th (absurd-clause tel ps) =
  absurd-clause <$> strengthenTelescope th tel <*> strengthenPatterns th ps

strengthenClauses th = traverseList (strengthenClause th)

strengthenTele f th emptyTel = just emptyTel
strengthenTele f th (extTel t ts) = extTel <$> f th t <*> strengthenTele f (keep th) ts

strengthenTelescope = strengthenTele (λ th → traverseDeco (strengthenArg th))

strengthenPattern th (con c ps) = con c <$> strengthenPatterns th ps
strengthenPattern th (dot t) = dot <$> strengthenTerm (th <> ones) t
strengthenPattern th (var v) = just (var v)
strengthenPattern th (lit l) = just (lit l)
strengthenPattern th (proj f) = just (proj f)
strengthenPattern th (absurd v) = just (absurd v)

strengthenPatterns th = traverseList (traverseArg (strengthenPattern th))

semidecidableEqFromBool : (A → A → Bool) →  SemidecidableEq A
semidecidableEqFromBool test x y with (test x y)
... | false = nothing
... | true = just trustMe

_≟Name_ : SemidecidableEq Name
_≟Name_ = semidecidableEqFromBool primQNameEquality

_≟Meta_ : SemidecidableEq Meta
_≟Meta_ = semidecidableEqFromBool primMetaEquality

_≟Float_ : SemidecidableEq Float
_≟Float_ = semidecidableEqFromBool primFloatEquality

_≟Char_ : SemidecidableEq Char
_≟Char_ = semidecidableEqFromBool primCharEquality

_≟String_ : SemidecidableEq String
_≟String_ = semidecidableEqFromBool primStringEquality

_≟Word64_ : SemidecidableEq Word64
_≟Word64_ = semidecidableEqFromBool λ w w' →
  primWord64ToNat w == primWord64ToNat w'


module SemidecidableEq where

  open MaybeBind

  semidecidableEqAbs : ∀ {T} → (∀ {n} → SemidecidableEq (T n)) →
                        SemidecidableEq (Abs T n)
  semidecidableEqAbs f (abs s b) (abs s' b') = do
    refl ← s ≟String s'
    refl ← f b b'
    just refl

  _≟Visibility_ : SemidecidableEq Visibility
  visible ≟Visibility visible = just refl
  hidden ≟Visibility hidden = just refl
  instance′ ≟Visibility instance′ = just refl
  _ ≟Visibility _ = nothing

  _≟Relevance_ : SemidecidableEq Relevance
  relevant ≟Relevance relevant = just refl
  irrelevant ≟Relevance irrelevant = just refl
  _ ≟Relevance _ = nothing

  _≟Quantity_ : SemidecidableEq Quantity
  quantity-0 ≟Quantity quantity-0 = just refl
  quantity-ω ≟Quantity quantity-ω = just refl
  _ ≟Quantity _ = nothing

  _≟Modality_ : SemidecidableEq Modality
  modality r q ≟Modality modality r' q' = do
    refl ← r ≟Relevance r'
    refl ← q ≟Quantity q'
    just refl

  _≟Var_ : SemidecidableEq (Var n)
  zero  ≟Var zero = just refl
  suc v ≟Var suc v' = do
    refl ← v ≟Var v'
    just refl
  _ ≟Var _ = nothing

  _≟Lit_ : SemidecidableEq Literal
  nat n ≟Lit nat n' = do
    refl ← n ≟ n'
    just refl
  word64 w ≟Lit word64 w' = do
    refl ← w ≟Word64 w'
    just refl
  float d ≟Lit float d' = do
    refl ← d ≟Float d'
    just refl
  char c ≟Lit char c' = do
    refl ← c ≟Char c'
    just refl
  string s ≟Lit string s' = do
    refl ← s ≟String s'
    just refl
  name nm ≟Lit name nm' = do
    refl ← nm ≟Name nm'
    just refl
  meta m ≟Lit meta m' = do
    refl ← m ≟Meta m'
    just refl
  _ ≟Lit _ = nothing

  _≟ArgInfo_ : SemidecidableEq ArgInfo
  arg-info v m ≟ArgInfo arg-info v' m' = do
    refl ← v ≟Visibility v'
    refl ← m ≟Modality m'
    just refl

  semidecidableEqTele : ∀ {T} → (∀ {n} → SemidecidableEq (T n)) → SemidecidableEq (Tele T n m)
  semidecidableEqTele eq emptyTel emptyTel = just refl
  semidecidableEqTele eq (extTel t ts) (extTel t' ts') = do
    refl ← eq t t'
    refl ← semidecidableEqTele eq ts ts'
    just refl

  semidecidableEqDeco : ∀ {T} → SemidecidableEq T → SemidecidableEq (String × T)
  semidecidableEqDeco eq (s , t) (s' , t') = do
    refl ← s ≟String s'
    refl ← eq t t'
    just refl

  semidecidableEqArg : ∀ {T} → SemidecidableEq T → SemidecidableEq (Arg T)
  semidecidableEqArg eq (arg i t) (arg i' t') = do
    refl ← i ≟ArgInfo i'
    refl ← eq t t'
    just refl

  {-# TERMINATING #-}
  _≟Term_      : SemidecidableEq (Term n)
  _≟Type_      : SemidecidableEq (Term n)
  _≟Sort_      : SemidecidableEq (Sort n)
  _≟Arg_       : SemidecidableEq (Arg (Term n))
  _≟Args_      : SemidecidableEq (List (Arg (Term n)))
  _≟Clause_    : SemidecidableEq (Clause n)
  _≟Clauses_   : SemidecidableEq (List (Clause n))
  _≟Telescope_ : SemidecidableEq (Telescope n m)
  _≟Pattern_   : SemidecidableEq (Pattern n m)
  _≟Patterns_  : SemidecidableEq (Patterns n m)

  var v args ≟Term var v' args' = do
    refl ← v ≟Var v'
    refl ← args ≟Args args'
    just refl
  con c args ≟Term con c' args' = do
    refl ← c ≟Name c'
    refl ← args ≟Args args'
    just refl
  def f args ≟Term def f' args' = do
    refl ← f ≟Name f'
    refl ← args ≟Args args'
    just refl
  lam v b ≟Term lam v' b' = do
    refl ← v ≟Visibility v'
    refl ← semidecidableEqAbs _≟Term_ b b'
    just refl
  pat-lam cs args ≟Term pat-lam cs' args' = do
    refl ← cs ≟Clauses cs'
    refl ← args ≟Args args'
    just refl
  pi a b ≟Term pi a' b' = do
    refl ← a ≟Arg a'
    refl ← semidecidableEqAbs _≟Term_ b b'
    just refl
  agda-sort s ≟Term agda-sort s' = do
    refl ← s ≟Sort s'
    just refl
  lit l ≟Term lit l' = do
    refl ← l ≟Lit l'
    just refl
  meta m args ≟Term meta m' args' = do
    refl ← m ≟Meta m'
    refl ← args ≟Args args'
    just refl
  unknown ≟Term unknown = just refl
  _ ≟Term _ = nothing

  _≟Type_ = _≟Term_

  set t ≟Sort set t' = do
    refl ← t ≟Term t'
    just refl
  lit l ≟Sort lit l' = do
    refl ← l ≟ l'
    just refl
  prop t ≟Sort prop t' = do
    refl ← t ≟Term t'
    just refl
  propLit l ≟Sort propLit l' = do
    refl ← l ≟ l'
    just refl
  inf m ≟Sort inf m' = do
    refl ← m ≟ m'
    just refl
  unknown ≟Sort unknown = just refl
  _ ≟Sort _ = nothing

  _≟Arg_ = semidecidableEqArg _≟Term_

  [] ≟Args [] = just refl
  (a ∷ as) ≟Args (a' ∷ as') = do
    refl ← a ≟Arg a'
    refl ← as ≟Args as'
    just refl
  _ ≟Args _ = nothing


  clause {m} tel ps t ≟Clause clause {m = m'} tel' ps' t' = do
    refl ← m ≟ m'
    refl ← tel ≟Telescope tel'
    refl ← ps ≟Patterns ps'
    refl ← t ≟Term t'
    just refl
  absurd-clause {m} tel ps ≟Clause absurd-clause {m = m'} tel' ps' = do
    refl ← m ≟ m'
    refl ← tel ≟Telescope tel'
    refl ← ps ≟Patterns ps'
    just refl
  _ ≟Clause _ = nothing

  [] ≟Clauses [] = just refl
  (cl ∷ cls) ≟Clauses (cl' ∷ cls') = do
    refl ← cl ≟Clause cl'
    refl ← cls ≟Clauses cls'
    just refl
  _ ≟Clauses _ = nothing

  _≟Telescope_ = semidecidableEqTele (semidecidableEqDeco _≟Arg_)

  con c ps ≟Pattern con c' ps' = do
    refl ← c ≟Name c'
    refl ← ps ≟Patterns ps'
    just refl
  dot t ≟Pattern dot t' = do
    refl ← t ≟Term t'
    just refl
  var v ≟Pattern var v' = do
    refl ← v ≟Var v'
    just refl
  lit l ≟Pattern lit l' = do
    refl ← l ≟Lit l'
    just refl
  proj f ≟Pattern proj f' = do
    refl ← f ≟Name f'
    just refl
  absurd v ≟Pattern absurd v' = do
    refl ← v ≟Var v'
    just refl
  _ ≟Pattern _ = nothing

  [] ≟Patterns [] = just refl
  (p ∷ ps) ≟Patterns (p' ∷ ps') = do
    refl ← semidecidableEqArg _≟Pattern_ p p'
    refl ← ps ≟Patterns ps'
    just refl
  _ ≟Patterns _ = nothing

open SemidecidableEq public

module Example where

  macro

    quot : A → R.Term → R.TC _
    quot a goal = do
      t ← R.quoteTC a
      q ← R.quoteTC t
      R.unify goal q
      where
      _>>=_ = R.bindTC

    scp : A → R.Term → R.TC _
    scp a goal = R.withNormalisation true do
      cxt ← R.getContext
      let n = length cxt
      t ← R.quoteTC a
      just t ← R.returnTC (scopeCheckTerm {n = n} t)
        where nothing → R.typeError []
      q ← R.quoteTC t
      R.unify goal q
      where
      _>>=_ = R.bindTC
      -- _=<<_ = λ k m → R.bindTC m k

  id : ∀{ℓ} (A : Set ℓ) → A → A
  id A x = x

  -- example₀ : Term 0
  -- example₀ = {!scp (λ (x : Nat) → x + (λ y → y) x)!}

  -- example : (z : Nat) → Term 1
  -- example z = {!scp λ (y : Nat) → (id (Nat → Nat) λ{ Nat.zero → Nat.zero; (Nat.suc x) → x + y + z})!}

-- Definitions --

data Definition : Set where
  function    : (cs : List (Clause 0)) → Definition
  data-type   : (pars : Nat) (cs : List Name) → Definition
  record-type : (c : Name) (fs : List (Arg Name)) → Definition
  data-cons   : (d : Name) → Definition
  axiom       : Definition
  prim-fun    : Definition

scopeCheckDefinition : R.Definition → Maybe (Definition)
scopeCheckDefinition (R.function cs) = function <$> traverseList scopeCheckClause cs
scopeCheckDefinition (R.data-type pars cs) = just (data-type pars cs)
scopeCheckDefinition (R.record-type c fs) = just (record-type c fs)
scopeCheckDefinition (R.data-cons d) = just (data-cons d)
scopeCheckDefinition R.axiom = just axiom
scopeCheckDefinition R.prim-fun = just prim-fun

-- {-# BUILTIN AGDADEFINITION                Definition  #-}
-- {-# BUILTIN AGDADEFINITIONFUNDEF          function    #-}
-- {-# BUILTIN AGDADEFINITIONDATADEF         data-type   #-}
-- {-# BUILTIN AGDADEFINITIONRECORDDEF       record-type #-}
-- {-# BUILTIN AGDADEFINITIONDATACONSTRUCTOR data-cons   #-}
-- {-# BUILTIN AGDADEFINITIONPOSTULATE       axiom       #-}
-- {-# BUILTIN AGDADEFINITIONPRIMITIVE       prim-fun    #-}

-- Errors --

data ErrorPart (n : Nat) : Set where
  strErr  : (s : String) → ErrorPart n
  termErr : (t : Term n) → ErrorPart n
  pattErr : -- TODO: we need names for the pattern variables, don't we?
            -- Tele (λ _ → String) n m →
            (p : Pattern n m) → ErrorPart n
  nameErr : (x : Name) → ErrorPart n

-- {-# BUILTIN AGDAERRORPART       ErrorPart #-}
-- {-# BUILTIN AGDAERRORPARTSTRING strErr    #-}
-- {-# BUILTIN AGDAERRORPARTTERM   termErr   #-}
-- {-# BUILTIN AGDAERRORPARTPATT   pattErr   #-}
-- {-# BUILTIN AGDAERRORPARTNAME   nameErr   #-}

unscopeErrorPart : ErrorPart n → R.ErrorPart
unscopeErrorPart (strErr s) = R.strErr s
unscopeErrorPart (termErr t) = R.termErr (unscopeTerm t)
unscopeErrorPart (pattErr p) = R.pattErr (unscopePattern p)
unscopeErrorPart (nameErr x) = R.nameErr x

-- TODO: sort out pattErr
-- scopeCheckErrorPart : ScopeCheck R.ErrorPart ErrorPart
-- scopeCheckErrorPart (R.strErr s) = just (strErr s)
-- scopeCheckErrorPart (R.termErr t) = termErr <$> scopeCheckTerm t
-- scopeCheckErrorPart (R.pattErr p) = pattErr <$> scopeCheckPattern p -- TODO
-- scopeCheckErrorPart (R.nameErr x) = just (nameErr x)

-- TC monad --

record TC {a} (n : Nat) (A : Set a) :  Set a where
  constructor mkTC
  field unTC : R.TC A
open TC

returnTC : ∀ {a} {A : Set a} → A → TC n A
returnTC a .unTC = R.returnTC a

bindTC : ∀ {a b} {A : Set a} {B : Set b} → TC n A → (A → TC n B) → TC n B
bindTC m k .unTC = R.bindTC (m .unTC) λ a → k a .unTC

private
  bindRTC : ∀ {a b} {A : Set a} {B : Set b} → R.TC A → (A → TC n B) → TC n B
  bindRTC m k .unTC = R.bindTC m λ a → k a .unTC

unify : Term n → Term n → TC n ⊤
unify t u .unTC = R.unify (unscopeTerm t) (unscopeTerm u)

runScopeCheck : Maybe A → TC n A -- {A : Nat → Set} → Maybe (A n) → TC n (A n)
runScopeCheck nothing .unTC  = R.typeError (R.strErr "Ill-scoped term" ∷ [])
runScopeCheck (just a) = returnTC a

recoverScope : R.TC R.Term → TC n (Term n)
recoverScope m = bindRTC m λ t → runScopeCheck (scopeCheckTerm t)

recoverScope' : {B : Nat → Set} → ScopeCheck A B → R.TC A → TC n (B n)
recoverScope' f m = bindRTC m λ a → runScopeCheck (f a)

typeError : ∀ {a} {A : Set a} → List (ErrorPart n) → TC n A
typeError es .unTC = R.typeError (map unscopeErrorPart es)

inferType : Term n → TC n (Type n)
inferType t =
  recoverScope (R.inferType (unscopeTerm t))

checkType : Term n → Type n → TC n (Term n)
checkType t T =
  recoverScope (R.checkType (unscopeTerm t) (unscopeTerm T))

normalise : Term n → TC n (Term n)
normalise t = recoverScope (R.normalise (unscopeTerm t))

reduce : Term n → TC n (Term n)
reduce t = recoverScope (R.reduce (unscopeTerm t))

catchTC : ∀ {a} {A : Set a} → TC n A → TC n A → TC n A
catchTC m h .unTC = R.catchTC (m .unTC) (h .unTC)

quoteTC : ∀ {a} {A : Set a} → A → TC n (Term n)
quoteTC a = recoverScope (R.quoteTC a)

unquoteTC : ∀ {a} {A : Set a} → Term n → TC n A
unquoteTC t .unTC = R.unquoteTC (unscopeTerm t)

quoteωTC : ∀ {A : Setω} → A → TC n (Term n)
quoteωTC a = recoverScope (R.quoteωTC a)

getContext : TC n (Telescope 0 n)
getContext {n = n} .unTC = do
  cxt ← R.getContext
  let m  = length cxt
  just refl ← R.returnTC (n ≟ m)
    where nothing → R.typeError []
  just tel ← R.returnTC (scopeCheckTelescope {n = 0} cxt)
    where nothing → R.typeError []
  R.returnTC tel
  where
  _>>=_ = R.bindTC

extendContext : ∀ {a} {A : Set a} → String → Arg (Type n) → TC (suc n) A → TC n A
extendContext s a m .unTC = R.extendContext s (mapArg unscopeTerm a) (m .unTC)

inContext : ∀ {a} {A : Set a} → Telescope 0 m → TC m A → TC n A
inContext tel m .unTC = R.inContext (unscopeTelescope tel) (m .unTC)

freshName : String → TC n Name
freshName s .unTC = R.freshName s

declareDef : Arg Name → Type n → TC n ⊤
declareDef x t .unTC = R.declareDef x (unscopeTerm t)

declarePostulate : Arg Name → Type n → TC n ⊤
declarePostulate x t .unTC = R.declarePostulate x (unscopeTerm t)

declareData : Name → (pars : Nat) → Type n → TC n ⊤
declareData x pars t .unTC = R.declareData x pars (unscopeTerm t)

defineData : Name → (pars : Nat) → List (Σ Name (λ _ → Type (n + pars))) → TC n ⊤
defineData x pars args .unTC = R.defineData x (map (λ (n , t) → n , unscopeTerm t) args)

defineFun : Name → List (Clause n) → TC n ⊤
defineFun n lc .unTC = R.defineFun n (map unscopeClause lc)

getType : Name → TC n (Type n)
getType nm  = recoverScope (R.getType nm)

getDefinition : Name → TC n Definition
getDefinition nm = recoverScope' scopeCheckDefinition (R.getDefinition nm)

blockOnMeta : ∀ {a} {A : Set a} → Meta → TC n A
blockOnMeta m .unTC = R.blockOnMeta m

commitTC : TC n ⊤
commitTC .unTC = R.commitTC

isMacro : Name → TC n Bool
isMacro nm .unTC = R.isMacro nm

-- If the argument is 'true' makes the following primitives also normalise
-- their results: inferType, checkType, quoteTC, getType, and getContext
withNormalisation : ∀ {a} {A : Set a} → Bool → TC n A → TC n A
withNormalisation b m .unTC = R.withNormalisation b (m .unTC)

-- Makes the following primitives to reconstruct hidden arguments
-- getDefinition, normalise, reduce, inferType, checkType and getContext
withReconstructed : ∀ {a} {A : Set a} → TC n A → TC n A
withReconstructed m .unTC = R.withReconstructed (m .unTC)

formatErrorParts : List (ErrorPart n) → TC n String
formatErrorParts es .unTC = R.formatErrorParts (map unscopeErrorPart es)

-- Prints the third argument if the corresponding verbosity level is turned
-- on (with the -v flag to Agda).
debugPrint : String → Nat → List (ErrorPart n) → TC n ⊤
debugPrint msg verbosity es .unTC = R.debugPrint msg verbosity (map unscopeErrorPart es)

-- Only allow reduction of specific definitions while executing the TC computation
onlyReduceDefs : ∀ {a} {A : Set a} → List Name → TC n A → TC n A
onlyReduceDefs xs m .unTC = R.onlyReduceDefs xs (m .unTC)

-- Don't allow reduction of specific definitions while executing the TC computation
dontReduceDefs : ∀ {a} {A : Set a} → List Name → TC n A → TC n A
dontReduceDefs xs m .unTC = R.dontReduceDefs xs (m .unTC)

-- Fail if the given computation gives rise to new, unsolved
-- "blocking" constraints.
noConstraints : ∀ {a} {A : Set a} → TC n A → TC n A
noConstraints m .unTC = R.noConstraints (m .unTC)

-- Run the given TC action and return the first component. Resets to
-- the old TC state if the second component is 'false', or keep the
-- new TC state if it is 'true'.
runSpeculative : ∀ {a} {A : Set a} → TC n (A × Bool) → TC n A
runSpeculative m .unTC = R.runSpeculative (m .unTC)

-- Get a list of all possible instance candidates for the given meta
-- variable (it does not have to be an instance meta).
getInstances : Meta → TC n (List (Term n))
getInstances x = recoverScope' (λ{n = n} → traverseList (scopeCheckTerm {n = n})) (R.getInstances x)

-- {-# BUILTIN AGDATCM                           TC                         #-}
-- {-# BUILTIN AGDATCMRETURN                     returnTC                   #-}
-- {-# BUILTIN AGDATCMBIND                       bindTC                     #-}
-- {-# BUILTIN AGDATCMUNIFY                      unify                      #-}
-- {-# BUILTIN AGDATCMTYPEERROR                  typeError                  #-}
-- {-# BUILTIN AGDATCMINFERTYPE                  inferType                  #-}
-- {-# BUILTIN AGDATCMCHECKTYPE                  checkType                  #-}
-- {-# BUILTIN AGDATCMNORMALISE                  normalise                  #-}
-- {-# BUILTIN AGDATCMREDUCE                     reduce                     #-}
-- {-# BUILTIN AGDATCMCATCHERROR                 catchTC                    #-}
-- {-# BUILTIN AGDATCMQUOTETERM                  quoteTC                    #-}
-- {-# BUILTIN AGDATCMUNQUOTETERM                unquoteTC                  #-}
-- {-# BUILTIN AGDATCMQUOTEOMEGATERM             quoteωTC                   #-}
-- {-# BUILTIN AGDATCMGETCONTEXT                 getContext                 #-}
-- {-# BUILTIN AGDATCMEXTENDCONTEXT              extendContext              #-}
-- {-# BUILTIN AGDATCMINCONTEXT                  inContext                  #-}
-- {-# BUILTIN AGDATCMFRESHNAME                  freshName                  #-}
-- {-# BUILTIN AGDATCMDECLAREDEF                 declareDef                 #-}
-- {-# BUILTIN AGDATCMDECLAREPOSTULATE           declarePostulate           #-}
-- {-# BUILTIN AGDATCMDECLAREDATA                declareData                #-}
-- {-# BUILTIN AGDATCMDEFINEDATA                 defineData                 #-}
-- {-# BUILTIN AGDATCMDEFINEFUN                  defineFun                  #-}
-- {-# BUILTIN AGDATCMGETTYPE                    getType                    #-}
-- {-# BUILTIN AGDATCMGETDEFINITION              getDefinition              #-}
-- {-# BUILTIN AGDATCMBLOCKONMETA                blockOnMeta                #-}
-- {-# BUILTIN AGDATCMCOMMIT                     commitTC                   #-}
-- {-# BUILTIN AGDATCMISMACRO                    isMacro                    #-}
-- {-# BUILTIN AGDATCMWITHNORMALISATION          withNormalisation          #-}
-- {-# BUILTIN AGDATCMFORMATERRORPARTS           formatErrorParts           #-}
-- {-# BUILTIN AGDATCMDEBUGPRINT                 debugPrint                 #-}
-- {-# BUILTIN AGDATCMONLYREDUCEDEFS             onlyReduceDefs             #-}
-- {-# BUILTIN AGDATCMDONTREDUCEDEFS             dontReduceDefs             #-}
-- {-# BUILTIN AGDATCMWITHRECONSPARAMS           withReconstructed          #-}
-- {-# BUILTIN AGDATCMNOCONSTRAINTS              noConstraints              #-}
-- {-# BUILTIN AGDATCMRUNSPECULATIVE             runSpeculative             #-}
-- {-# BUILTIN AGDATCMGETINSTANCES               getInstances               #-}

-- All the TC primitives are compiled to functions that return
-- undefined, rather than just undefined, in an attempt to make sure
-- that code will run properly.
{-# COMPILE JS returnTC          = _ => _ => _ =>      undefined #-}
{-# COMPILE JS bindTC            = _ => _ => _ => _ =>
                                   _ => _ =>           undefined #-}
{-# COMPILE JS unify             = _ => _ =>           undefined #-}
{-# COMPILE JS typeError         = _ => _ => _ =>      undefined #-}
{-# COMPILE JS inferType         = _ =>                undefined #-}
{-# COMPILE JS checkType         = _ => _ =>           undefined #-}
{-# COMPILE JS normalise         = _ =>                undefined #-}
{-# COMPILE JS reduce            = _ =>                undefined #-}
{-# COMPILE JS catchTC           = _ => _ => _ => _ => undefined #-}
{-# COMPILE JS quoteTC           = _ => _ => _ =>      undefined #-}
{-# COMPILE JS unquoteTC         = _ => _ => _ =>      undefined #-}
{-# COMPILE JS quoteωTC          = _ => _ =>           undefined #-}
{-# COMPILE JS getContext        =                     undefined #-}
{-# COMPILE JS extendContext     = _ => _ => _ => _ => _ => undefined #-}
{-# COMPILE JS inContext         = _ => _ => _ => _ => undefined #-}
{-# COMPILE JS freshName         = _ =>                undefined #-}
{-# COMPILE JS declareDef        = _ => _ =>           undefined #-}
{-# COMPILE JS declarePostulate  = _ => _ =>           undefined #-}
{-# COMPILE JS declareData       = _ => _ => _ =>      undefined #-}
{-# COMPILE JS defineData        = _ => _ =>           undefined #-}
{-# COMPILE JS defineFun         = _ => _ =>           undefined #-}
{-# COMPILE JS getType           = _ =>                undefined #-}
{-# COMPILE JS getDefinition     = _ =>                undefined #-}
{-# COMPILE JS blockOnMeta       = _ => _ => _ =>      undefined #-}
{-# COMPILE JS commitTC          =                     undefined #-}
{-# COMPILE JS isMacro           = _ =>                undefined #-}
{-# COMPILE JS withNormalisation = _ => _ => _ => _ => undefined #-}
{-# COMPILE JS withReconstructed = _ => _ => _ =>      undefined #-}
{-# COMPILE JS debugPrint        = _ => _ => _ =>      undefined #-}
{-# COMPILE JS onlyReduceDefs    = _ => _ => _ => _ => undefined #-}
{-# COMPILE JS dontReduceDefs    = _ => _ => _ => _ => undefined #-}
{-# COMPILE JS noConstraints     = _ => _ => _ =>      undefined #-}
{-# COMPILE JS runSpeculative    = _ => _ => _ =>      undefined #-}
{-# COMPILE JS getInstances      = _ =>                undefined #-}

mkMacro : (∀ {n} → Term n → TC n ⊤) → R.Term → R.TC ⊤
mkMacro f hole = R.bindTC R.getContext λ ctx →
  let n = length ctx in
  TC.unTC {n = n} (let _>>=_ = bindTC in do
    just t ← returnTC (scopeCheckTerm hole)
      where nothing → mkTC (R.typeError (R.strErr "The IMPOSSIBLE has happened" ∷ []))
    f t)

record Kit (Rep : Nat → Set) : Set where
  field
    reify : Rep m → List (Arg (Term m)) → Term m
    thin  : Thin m n → Rep m → Rep n
    var₀  : Rep (suc m)

module Replace {Rep} (k : Kit Rep) where

  open Kit k

  _⇑ : (Var m → Rep n) →
       (Var (suc m) → Rep (suc n))
  (ρ ⇑) zero = var₀
  (ρ ⇑) (suc v) = thin (skip ones) (ρ v)

  _⟰_ : (Var m → Rep n) → (p : Nat) →
         (Var (m + p) → Rep (n + p))
  ρ ⟰ zero = subst₂ (λ m n → (Var m → Rep n)) trustMe trustMe ρ
  ρ ⟰ suc m = subst₂ (λ m n → (Var m → Rep n)) trustMe trustMe ((ρ ⇑) ⟰ m)

  Replaceable : (Nat → Set) → Set
  Replaceable T = ∀ {m n} → (Var m → Rep n) → T m → T n

  {-# TERMINATING #-}
  replaceTerm      : Replaceable Term
  replaceType      : Replaceable Type
  replaceArg       : ∀ {T} → Replaceable T → Replaceable (λ n → Arg (T n))
  replaceArgs      : ∀ {T} → Replaceable T → Replaceable (λ n → List (Arg (T n)))
  replaceAbs       : ∀ {T} → Replaceable T → Replaceable (Abs T)
  replaceTele      : ∀ {T} → Replaceable T → Replaceable (λ n → Tele T n m)
  replaceDeco      : ∀ {A T} → Replaceable T → Replaceable (λ n → A × T n)
  replaceTelescope : Replaceable (λ n → Telescope n m)
  replaceSort      : Replaceable Sort
  replaceClause    : Replaceable Clause
  replacePattern   : Replaceable (λ n → Pattern n m)
  replacePatterns  : Replaceable (λ n → Patterns n m)

  replaceTerm ρ (var v args) = reify (ρ v) (replaceArgs replaceTerm ρ args)
  replaceTerm ρ (con c args) = con c (replaceArgs replaceTerm ρ args)
  replaceTerm ρ (def f args) = def f (replaceArgs replaceTerm ρ args)
  replaceTerm ρ (lam v t) = lam v (replaceAbs replaceTerm ρ t)
  replaceTerm ρ (pat-lam cs args) = pat-lam (map (replaceClause ρ) cs) (replaceArgs replaceTerm ρ args)
  replaceTerm ρ (pi a b) = pi (replaceArg replaceTerm ρ a) (replaceAbs replaceType ρ b)
  replaceTerm ρ (agda-sort s) = agda-sort (replaceSort ρ s)
  replaceTerm ρ (lit l) = lit l
  replaceTerm ρ (meta v args) = meta v (replaceArgs replaceTerm ρ args)
  replaceTerm ρ unknown = unknown

  replaceArg f ρ = mapArg (f ρ)
  replaceArgs f ρ = map (replaceArg f ρ)

  replaceAbs f ρ (abs x t) = abs x (f (ρ ⇑) t)

  replaceType = replaceTerm

  replaceSort ρ (set t) = set (replaceTerm ρ t)
  replaceSort ρ (lit m) = lit m
  replaceSort ρ (prop t) = prop (replaceTerm ρ t)
  replaceSort ρ (propLit m) = lit m
  replaceSort ρ (inf m) = lit m
  replaceSort ρ unknown = unknown

  replaceClause ρ (clause {m = m} tel ps t) =
    clause (replaceTelescope ρ tel) (replacePatterns ρ ps) (replaceTerm (ρ ⟰ m) t)
  replaceClause ρ (absurd-clause tel ps) = absurd-clause (replaceTelescope ρ tel) (replacePatterns ρ ps)

  replaceTele f ρ emptyTel = emptyTel
  replaceTele f ρ (extTel t tel) = extTel (f ρ t) (replaceTele f (ρ ⇑) tel)

  replaceDeco f ρ (a , t) = (a , f ρ t)

  replaceTelescope = replaceTele (replaceDeco (replaceArg replaceTerm))

  replacePattern ρ (con c ps) = con c (replacePatterns ρ ps)
  replacePattern {m} ρ (dot t) = dot (replaceTerm (ρ ⟰ m) t)
  replacePattern ρ (var v) = var v
  replacePattern ρ (lit l) = lit l
  replacePattern ρ (proj f) = proj f
  replacePattern ρ (absurd v) = absurd v

  replacePatterns = replaceArgs replacePattern


thVar : Thin m n → Var m → Var n
thVar (skip th) v = suc (thVar th v)
thVar (keep th) zero = zero
thVar (keep th) (suc v) = suc (thVar th v)

renKit : Kit Var
renKit .Kit.reify = var
renKit .Kit.thin = thVar
renKit .Kit.var₀ = zero

renTerm : (Var m → Var n) → Term m → Term n
renTerm = Replace.replaceTerm renKit

-- Hereditary subst because Terms are in NF
-- TODO: make the setup partial?
{-# TERMINATING #-}
subKit    : Kit Term
subTerm   : (Var m → Term n) → Term m → Term n
applyTerm : Term m → List (Arg (Term m)) → Term m

subKit .Kit.reify = applyTerm
subKit .Kit.thin = λ th → renTerm (thVar th)
subKit .Kit.var₀ = var zero []

subTerm = Replace.replaceTerm subKit

[_/0] : Term m → (Var (suc m) → Term m)
[ t /0] zero = t
[ t /0] (suc v) = var v []

applyAbs : Abs Term n → Term n → Term n
applyAbs (abs s b) t = subTerm [ t /0] b

applyTerm t [] = t
applyTerm (var v args) ts = var v (args ++ ts)
applyTerm (con c args) ts = con c (args ++ ts)
applyTerm (def f args) ts = def f (args ++ ts)
applyTerm (lam v b) (arg _ t ∷ ts) = applyTerm (applyAbs b t) ts
applyTerm (pat-lam cs args) ts = pat-lam cs (args ++ ts)
applyTerm (pi a b) ts = unknown
applyTerm (agda-sort s) ts = unknown
applyTerm (lit l) ts = unknown
applyTerm (meta m args) ts = meta m (args ++ ts)
applyTerm unknown ts = unknown

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
