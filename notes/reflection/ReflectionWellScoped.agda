-- {-# OPTIONS --cubical-compatible --safe --no-sized-types --no-guardedness #-}

-- Well-scoped de Bruijn indices in reflection

-- module Agda.Builtin.ReflectionWellScope where

open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Word
open import Agda.Builtin.List
open import Agda.Builtin.String
open import Agda.Builtin.Char
open import Agda.Builtin.Float
open import Agda.Builtin.Int
open import Agda.Builtin.Sigma
open import Agda.Primitive

-- Names --

postulate Name : Set
{-# BUILTIN QNAME Name #-}

primitive
  primQNameEquality : Name → Name → Bool
  primQNameLess     : Name → Name → Bool
  primShowQName     : Name → String

-- Fixity --

data Associativity : Set where
  left-assoc  : Associativity
  right-assoc : Associativity
  non-assoc   : Associativity

data Precedence : Set where
  related   : Float → Precedence
  unrelated : Precedence

data Fixity : Set where
  fixity : Associativity → Precedence → Fixity

{-# BUILTIN ASSOC      Associativity #-}
{-# BUILTIN ASSOCLEFT  left-assoc    #-}
{-# BUILTIN ASSOCRIGHT right-assoc   #-}
{-# BUILTIN ASSOCNON   non-assoc     #-}

{-# BUILTIN PRECEDENCE    Precedence #-}
{-# BUILTIN PRECRELATED   related    #-}
{-# BUILTIN PRECUNRELATED unrelated  #-}

{-# BUILTIN FIXITY       Fixity #-}
{-# BUILTIN FIXITYFIXITY fixity #-}

{-# COMPILE GHC Associativity = data MAlonzo.RTE.Assoc (MAlonzo.RTE.LeftAssoc | MAlonzo.RTE.RightAssoc | MAlonzo.RTE.NonAssoc) #-}
{-# COMPILE GHC Precedence    = data MAlonzo.RTE.Precedence (MAlonzo.RTE.Related | MAlonzo.RTE.Unrelated) #-}
{-# COMPILE GHC Fixity        = data MAlonzo.RTE.Fixity (MAlonzo.RTE.Fixity) #-}

{-# COMPILE JS Associativity  = function (x,v) { return v[x](); } #-}
{-# COMPILE JS left-assoc     = "left-assoc"  #-}
{-# COMPILE JS right-assoc    = "right-assoc" #-}
{-# COMPILE JS non-assoc      = "non-assoc"   #-}

{-# COMPILE JS Precedence     =
  function (x,v) {
    if (x === "unrelated") { return v[x](); } else { return v["related"](x); }} #-}
{-# COMPILE JS related        = function(x) { return x; } #-}
{-# COMPILE JS unrelated      = "unrelated"               #-}

{-# COMPILE JS Fixity         = function (x,v) { return v["fixity"](x["assoc"], x["prec"]); } #-}
{-# COMPILE JS fixity         = function (x) { return function (y) { return { "assoc": x, "prec": y}; }; } #-}

primitive
  primQNameFixity : Name → Fixity
  primQNameToWord64s : Name → Σ Word64 (λ _ → Word64)

-- Metavariables --

postulate Meta : Set
{-# BUILTIN AGDAMETA Meta #-}

primitive
  primMetaEquality : Meta → Meta → Bool
  primMetaLess     : Meta → Meta → Bool
  primShowMeta     : Meta → String
  primMetaToNat    : Meta → Nat

-- Arguments --

-- Arguments can be (visible), {hidden}, or {{instance}}.
data Visibility : Set where
  visible hidden instance′ : Visibility

{-# BUILTIN HIDING   Visibility #-}
{-# BUILTIN VISIBLE  visible    #-}
{-# BUILTIN HIDDEN   hidden     #-}
{-# BUILTIN INSTANCE instance′  #-}

-- Arguments can be relevant or irrelevant.
data Relevance : Set where
  relevant irrelevant : Relevance

{-# BUILTIN RELEVANCE  Relevance  #-}
{-# BUILTIN RELEVANT   relevant   #-}
{-# BUILTIN IRRELEVANT irrelevant #-}

-- Arguments also have a quantity.
data Quantity : Set where
  quantity-0 quantity-ω : Quantity

{-# BUILTIN QUANTITY   Quantity   #-}
{-# BUILTIN QUANTITY-0 quantity-0 #-}
{-# BUILTIN QUANTITY-ω quantity-ω #-}

-- Relevance and quantity are combined into a modality.
data Modality : Set where
  modality : (r : Relevance) (q : Quantity) → Modality

{-# BUILTIN MODALITY             Modality #-}
{-# BUILTIN MODALITY-CONSTRUCTOR modality #-}

data ArgInfo : Set where
  arg-info : (v : Visibility) (m : Modality) → ArgInfo

data Arg {a} (A : Set a) : Set a where
  arg : (i : ArgInfo) (x : A) → Arg A

{-# BUILTIN ARGINFO    ArgInfo  #-}
{-# BUILTIN ARGARGINFO arg-info #-}
{-# BUILTIN ARG        Arg      #-}
{-# BUILTIN ARGARG     arg      #-}

-- Name abstraction --

variable
  n m : Nat

data Abs {a} (A : Nat → Set a) (n : Nat) : Set a where
  abs : (s : String) (x : A (suc n)) → Abs A n

-- {-# BUILTIN ABS    Abs #-}
-- {-# BUILTIN ABSABS abs #-}

-- Literals --

data Literal : Set where
  nat    : (n : Nat)    → Literal
  word64 : (n : Word64) → Literal
  float  : (x : Float)  → Literal
  char   : (c : Char)   → Literal
  string : (s : String) → Literal
  name   : (x : Name)   → Literal
  meta   : (x : Meta)   → Literal

{-# BUILTIN AGDALITERAL   Literal #-}
{-# BUILTIN AGDALITNAT    nat     #-}
{-# BUILTIN AGDALITWORD64 word64  #-}
{-# BUILTIN AGDALITFLOAT  float   #-}
{-# BUILTIN AGDALITCHAR   char    #-}
{-# BUILTIN AGDALITSTRING string  #-}
{-# BUILTIN AGDALITQNAME  name    #-}
{-# BUILTIN AGDALITMETA   meta    #-}

-- Variables --

data Var : Nat → Set where
  zero : ∀{n} → Var (suc n)
  suc  : ∀{n} → (x : Var n) → Var (suc n)

-- Terms and patterns --

data Term (n : Nat) : Set
data Sort (n : Nat) : Set
data Pattern (n m : Nat) : Set
data Clause (n : Nat) : Set
Type = Term

data Tele (A : Nat → Set) (n : Nat) : Nat → Set where
  emptyTel : Tele A n zero
  extTel   : A n → Tele A (suc n) m → Tele A n (suc m)

private
  _×_ : ∀{ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set _
  A × B = Σ A λ _ → B

Telescope : (n m : Nat) → Set
Telescope = Tele (λ k → String × Arg (Type k))

-- data Telescope (n : Nat) : Nat → Set where
--   emptyTel : Telescope n zero
--   extTel   : String → Arg (Type n) → Telescope (suc n) m → Telescope n (suc m)

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

-- Definitions --

data Definition : Set where
  function    : (cs : List (Clause 0)) → Definition
  data-type   : (pars : Nat) (cs : List Name) → Definition
  record-type : (c : Name) (fs : List (Arg Name)) → Definition
  data-cons   : (d : Name) → Definition
  axiom       : Definition
  prim-fun    : Definition

-- {-# BUILTIN AGDADEFINITION                Definition  #-}
-- {-# BUILTIN AGDADEFINITIONFUNDEF          function    #-}
-- {-# BUILTIN AGDADEFINITIONDATADEF         data-type   #-}
-- {-# BUILTIN AGDADEFINITIONRECORDDEF       record-type #-}
-- {-# BUILTIN AGDADEFINITIONDATACONSTRUCTOR data-cons   #-}
-- {-# BUILTIN AGDADEFINITIONPOSTULATE       axiom       #-}
-- {-# BUILTIN AGDADEFINITIONPRIMITIVE       prim-fun    #-}

-- Errors --

data ErrorPart (n : Nat) : Set where
  strErr  : String → ErrorPart n
  termErr : Term n → ErrorPart n
  pattErr : Tele (λ _ → String) n m → Pattern n m → ErrorPart n
  nameErr : Name → ErrorPart n

-- {-# BUILTIN AGDAERRORPART       ErrorPart #-}
-- {-# BUILTIN AGDAERRORPARTSTRING strErr    #-}
-- {-# BUILTIN AGDAERRORPARTTERM   termErr   #-}
-- {-# BUILTIN AGDAERRORPARTPATT   pattErr   #-}
-- {-# BUILTIN AGDAERRORPARTNAME   nameErr   #-}

-- TC monad --

postulate
  TC               : ∀ {a} → Nat → Set a → Set a
  returnTC         : ∀ {a} {A : Set a} → A → TC n A
  bindTC           : ∀ {a b} {A : Set a} {B : Set b} → TC n A → (A → TC n B) → TC n B
  unify            : Term n → Term n → TC n ⊤
  typeError        : ∀ {a} {A : Set a} → List (ErrorPart n) → TC n A
  inferType        : Term n → TC n (Type n)
  checkType        : Term n → Type n → TC n (Term n)
  normalise        : Term n → TC n (Term n)
  reduce           : Term n → TC n (Term n)
  catchTC          : ∀ {a} {A : Set a} → TC n A → TC n A → TC n A
  quoteTC          : ∀ {a} {A : Set a} → A → TC n (Term n)
  unquoteTC        : ∀ {a} {A : Set a} → Term n → TC n A
  quoteωTC         : ∀ {A : Setω} → A → TC n (Term n)
  getContext       : TC n (Telescope 0 n)
  extendContext    : ∀ {a} {A : Set a} → String → Arg (Type n) → TC (suc n) A → TC n A
  inContext        : ∀ {a} {A : Set a} → Telescope 0 m → TC m A → TC n A
  freshName        : String → TC n Name
  declareDef       : Arg Name → Type n → TC n ⊤
  declarePostulate : Arg Name → Type n → TC n ⊤
  declareData      : Name → (pars : Nat) → Type n → TC n ⊤
  defineData       : Name → (pars : Nat) → List (Σ Name (λ _ → Type (n + pars))) → TC n ⊤
  defineFun        : Name → List (Clause n) → TC n ⊤
  getType          : Name → TC n (Type n)
  getDefinition    : Name → TC n Definition
  blockOnMeta      : ∀ {a} {A : Set a} → Meta → TC n A
  commitTC         : TC n ⊤
  isMacro          : Name → TC n Bool

  -- If the argument is 'true' makes the following primitives also normalise
  -- their results: inferType, checkType, quoteTC, getType, and getContext
  withNormalisation : ∀ {a} {A : Set a} → Bool → TC n A → TC n A

  -- Makes the following primitives to reconstruct hidden arguments
  -- getDefinition, normalise, reduce, inferType, checkType and getContext
  withReconstructed : ∀ {a} {A : Set a} → TC n A → TC n A

  formatErrorParts : List (ErrorPart n) → TC n String
  -- Prints the third argument if the corresponding verbosity level is turned
  -- on (with the -v flag to Agda).
  debugPrint : String → Nat → List (ErrorPart n) → TC n ⊤

  -- Only allow reduction of specific definitions while executing the TC computation
  onlyReduceDefs : ∀ {a} {A : Set a} → List Name → TC n A → TC n A

  -- Don't allow reduction of specific definitions while executing the TC computation
  dontReduceDefs : ∀ {a} {A : Set a} → List Name → TC n A → TC n A

  -- Fail if the given computation gives rise to new, unsolved
  -- "blocking" constraints.
  noConstraints : ∀ {a} {A : Set a} → TC n A → TC n A

  -- Run the given TC action and return the first component. Resets to
  -- the old TC state if the second component is 'false', or keep the
  -- new TC state if it is 'true'.
  runSpeculative : ∀ {a} {A : Set a} → TC n (A × Bool) → TC n A

  -- Get a list of all possible instance candidates for the given meta
  -- variable (it does not have to be an instance meta).
  getInstances : Meta → TC n (List (Term n))

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
