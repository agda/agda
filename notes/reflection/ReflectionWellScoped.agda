-- {-# OPTIONS --cubical-compatible --safe --no-sized-types --no-guardedness #-}

-- Well-scoped de Bruijn indices in reflection

-- module Agda.Builtin.ReflectionWellScope where

open import Agda.Primitive
open import Agda.Builtin.Bool
open import Agda.Builtin.Char
open import Agda.Builtin.Equality
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

  length : ∀{ℓ} {A : Set ℓ} → List A → Nat
  length [] = 0
  length (_ ∷ xs) = 1 + length xs

  map : (A → B) → List A → List B
  map f [] = []
  map f (x ∷ xs) = f x ∷ map f xs

  -- We do traversals in the Maybe Applicative.

  -- _>>=_ : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
  -- just x >>= k = k x
  -- nothing >>= k = nothing

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

  cong : {A B : Set} (f : A → B) {a b : A} → a ≡ b → f a ≡ f b
  cong f refl = refl

  _≟_ : (n m : Nat) → Maybe (n ≡ m)
  zero ≟ zero = just refl
  suc m ≟ zero = nothing
  zero ≟ suc n = nothing
  suc m ≟ suc n = cong suc <$> m ≟ n

-- Well-scoped de Bruijn indices version of Agda.Builtin.Reflection
------------------------------------------------------------------------

-- Name abstraction --

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
unscopePattern : Pattern n m → R.Pattern
unscopePatterns : Patterns n m → List (Arg R.Pattern)
unscopePatterns = map (mapArg unscopePattern)

unscopeClause (clause tel ps t) = R.clause (unscopeTelescope tel) (unscopePatterns ps) (unscopeTerm t)
unscopeClause (absurd-clause tel ps) = R.absurd-clause (unscopeTelescope tel) (unscopePatterns ps)

unscopeTelescope emptyTel = []
unscopeTelescope (extTel (s , t) tel) = (s , mapArg unscopeTerm t) ∷ unscopeTelescope tel

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
scopeCheckTelescope = scopeCheckTele (traverseDeco (traverseArg scopeCheckType))

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

postulate
  typeError        : ∀ {a} {A : Set a} → List (ErrorPart n) → TC n A

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
  just tel ← R.returnTC (scopeCheckTelescope cxt)
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


-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
