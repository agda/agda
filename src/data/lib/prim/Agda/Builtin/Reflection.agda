{-# OPTIONS --cubical-compatible --safe --no-sized-types --no-guardedness --level-universe --type-based-termination #-}

module Agda.Builtin.Reflection where

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

data Blocker : Set where
  blockerAny  : List Blocker → Blocker
  blockerAll  : List Blocker → Blocker
  blockerMeta : Meta → Blocker

{-# BUILTIN AGDABLOCKER     Blocker #-}
{-# BUILTIN AGDABLOCKERANY  blockerAny #-}
{-# BUILTIN AGDABLOCKERALL  blockerAll #-}
{-# BUILTIN AGDABLOCKERMETA blockerMeta #-}

-- Name abstraction --

data Abs {a} (A : Set a) : Set a where
  abs : (s : String) (x : A) → Abs A

{-# BUILTIN ABS    Abs #-}
{-# BUILTIN ABSABS abs #-}

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


-- Terms and patterns --

data Term    : Set
data Sort    : Set
data Pattern : Set
data Clause  : Set
Type = Term
Telescope = List (Σ String λ _ → Arg Type)

data Term where
  var       : (x : Nat) (args : List (Arg Term)) → Term
  con       : (c : Name) (args : List (Arg Term)) → Term
  def       : (f : Name) (args : List (Arg Term)) → Term
  lam       : (v : Visibility) (t : Abs Term) → Term
  pat-lam   : (cs : List Clause) (args : List (Arg Term)) → Term
  pi        : (a : Arg Type) (b : Abs Type) → Term
  agda-sort : (s : Sort) → Term
  lit       : (l : Literal) → Term
  meta      : (x : Meta) → List (Arg Term) → Term
  unknown   : Term

data Sort where
  set     : (t : Term) → Sort
  lit     : (n : Nat) → Sort
  prop    : (t : Term) → Sort
  propLit : (n : Nat) → Sort
  inf     : (n : Nat) → Sort
  unknown : Sort

data Pattern where
  con    : (c : Name) (ps : List (Arg Pattern)) → Pattern
  dot    : (t : Term)    → Pattern
  var    : (x : Nat)     → Pattern
  lit    : (l : Literal) → Pattern
  proj   : (f : Name)    → Pattern
  absurd : (x : Nat)     → Pattern  -- absurd patterns counts as variables

data Clause where
  clause        : (tel : Telescope) (ps : List (Arg Pattern)) (t : Term) → Clause
  absurd-clause : (tel : Telescope) (ps : List (Arg Pattern)) → Clause

{-# BUILTIN AGDATERM      Term    #-}
{-# BUILTIN AGDASORT      Sort    #-}
{-# BUILTIN AGDAPATTERN   Pattern #-}
{-# BUILTIN AGDACLAUSE    Clause  #-}

{-# BUILTIN AGDATERMVAR         var       #-}
{-# BUILTIN AGDATERMCON         con       #-}
{-# BUILTIN AGDATERMDEF         def       #-}
{-# BUILTIN AGDATERMMETA        meta      #-}
{-# BUILTIN AGDATERMLAM         lam       #-}
{-# BUILTIN AGDATERMEXTLAM      pat-lam   #-}
{-# BUILTIN AGDATERMPI          pi        #-}
{-# BUILTIN AGDATERMSORT        agda-sort #-}
{-# BUILTIN AGDATERMLIT         lit       #-}
{-# BUILTIN AGDATERMUNSUPPORTED unknown   #-}

{-# BUILTIN AGDASORTSET         set     #-}
{-# BUILTIN AGDASORTLIT         lit     #-}
{-# BUILTIN AGDASORTPROP        prop    #-}
{-# BUILTIN AGDASORTPROPLIT     propLit #-}
{-# BUILTIN AGDASORTINF         inf     #-}
{-# BUILTIN AGDASORTUNSUPPORTED unknown #-}

{-# BUILTIN AGDAPATCON    con     #-}
{-# BUILTIN AGDAPATDOT    dot     #-}
{-# BUILTIN AGDAPATVAR    var     #-}
{-# BUILTIN AGDAPATLIT    lit     #-}
{-# BUILTIN AGDAPATPROJ   proj    #-}
{-# BUILTIN AGDAPATABSURD absurd  #-}

{-# BUILTIN AGDACLAUSECLAUSE clause        #-}
{-# BUILTIN AGDACLAUSEABSURD absurd-clause #-}

-- Definitions --

data Definition : Set where
  function    : (cs : List Clause) → Definition
  data-type   : (pars : Nat) (cs : List Name) → Definition
  record-type : (c : Name) (fs : List (Arg Name)) → Definition
  data-cons   : (d : Name) → Definition
  axiom       : Definition
  prim-fun    : Definition

{-# BUILTIN AGDADEFINITION                Definition  #-}
{-# BUILTIN AGDADEFINITIONFUNDEF          function    #-}
{-# BUILTIN AGDADEFINITIONDATADEF         data-type   #-}
{-# BUILTIN AGDADEFINITIONRECORDDEF       record-type #-}
{-# BUILTIN AGDADEFINITIONDATACONSTRUCTOR data-cons   #-}
{-# BUILTIN AGDADEFINITIONPOSTULATE       axiom       #-}
{-# BUILTIN AGDADEFINITIONPRIMITIVE       prim-fun    #-}

-- Errors --

data ErrorPart : Set where
  strErr  : String → ErrorPart
  termErr : Term → ErrorPart
  pattErr : Pattern → ErrorPart
  nameErr : Name → ErrorPart

{-# BUILTIN AGDAERRORPART       ErrorPart #-}
{-# BUILTIN AGDAERRORPARTSTRING strErr    #-}
{-# BUILTIN AGDAERRORPARTTERM   termErr   #-}
{-# BUILTIN AGDAERRORPARTPATT   pattErr   #-}
{-# BUILTIN AGDAERRORPARTNAME   nameErr   #-}

-- TC monad --

postulate
  TC               : ∀ {a} → Set a → Set a
  returnTC         : ∀ {a} {A : Set a} → A → TC A
  bindTC           : ∀ {a b} {A : Set a} {B : Set b} → TC A → (A → TC B) → TC B
  unify            : Term → Term → TC ⊤
  typeError        : ∀ {a} {A : Set a} → List ErrorPart → TC A
  inferType        : Term → TC Type
  checkType        : Term → Type → TC Term
  normalise        : Term → TC Term
  reduce           : Term → TC Term
  catchTC          : ∀ {a} {A : Set a} → TC A → TC A → TC A
  quoteTC          : ∀ {a} {A : Set a} → A → TC Term
  unquoteTC        : ∀ {a} {A : Set a} → Term → TC A
  quoteωTC         : ∀ {A : Setω} → A → TC Term
  getContext       : TC Telescope
  extendContext    : ∀ {a} {A : Set a} → String → Arg Type → TC A → TC A
  inContext        : ∀ {a} {A : Set a} → Telescope → TC A → TC A
  freshName        : String → TC Name
  declareDef       : Arg Name → Type → TC ⊤
  declarePostulate : Arg Name → Type → TC ⊤
  declareData      : Name → Nat → Type → TC ⊤
  defineData       : Name → List (Σ Name (λ _ → Type)) → TC ⊤
  defineFun        : Name → List Clause → TC ⊤
  getType          : Name → TC Type
  getDefinition    : Name → TC Definition
  blockTC          : ∀ {a} {A : Set a} → Blocker → TC A
  commitTC         : TC ⊤
  isMacro          : Name → TC Bool
  pragmaForeign    : String → String → TC ⊤
  pragmaCompile    : String → Name → String → TC ⊤

  -- If 'true', makes the following primitives also normalise
  -- their results: inferType, checkType, quoteTC, getType, and getContext
  withNormalisation : ∀ {a} {A : Set a} → Bool → TC A → TC A
  askNormalisation  : TC Bool

  -- If 'true', makes the following primitives to reconstruct hidden arguments:
  -- getDefinition, normalise, reduce, inferType, checkType and getContext
  withReconstructed : ∀ {a} {A : Set a} → Bool → TC A → TC A
  askReconstructed  : TC Bool

  -- Whether implicit arguments at the end should be turned into metavariables
  withExpandLast : ∀ {a} {A : Set a} → Bool → TC A → TC A
  askExpandLast  : TC Bool

  -- White/blacklist specific definitions for reduction while executing the TC computation
  -- 'true' for whitelist, 'false' for blacklist
  withReduceDefs : ∀ {a} {A : Set a} → (Σ Bool λ _ → List Name) → TC A → TC A
  askReduceDefs  : TC (Σ Bool λ _ → List Name)

  formatErrorParts : List ErrorPart → TC String
  -- Prints the third argument if the corresponding verbosity level is turned
  -- on (with the -v flag to Agda).
  debugPrint : String → Nat → List ErrorPart → TC ⊤

  -- Fail if the given computation gives rise to new, unsolved
  -- "blocking" constraints.
  noConstraints : ∀ {a} {A : Set a} → TC A → TC A

  -- Run the given TC action and return the first component. Resets to
  -- the old TC state if the second component is 'false', or keep the
  -- new TC state if it is 'true'.
  runSpeculative : ∀ {a} {A : Set a} → TC (Σ A λ _ → Bool) → TC A

  -- Get a list of all possible instance candidates for the given meta
  -- variable (it does not have to be an instance meta).
  getInstances : Meta → TC (List Term)

{-# BUILTIN AGDATCM                           TC                         #-}
{-# BUILTIN AGDATCMRETURN                     returnTC                   #-}
{-# BUILTIN AGDATCMBIND                       bindTC                     #-}
{-# BUILTIN AGDATCMUNIFY                      unify                      #-}
{-# BUILTIN AGDATCMTYPEERROR                  typeError                  #-}
{-# BUILTIN AGDATCMINFERTYPE                  inferType                  #-}
{-# BUILTIN AGDATCMCHECKTYPE                  checkType                  #-}
{-# BUILTIN AGDATCMNORMALISE                  normalise                  #-}
{-# BUILTIN AGDATCMREDUCE                     reduce                     #-}
{-# BUILTIN AGDATCMCATCHERROR                 catchTC                    #-}
{-# BUILTIN AGDATCMQUOTETERM                  quoteTC                    #-}
{-# BUILTIN AGDATCMUNQUOTETERM                unquoteTC                  #-}
{-# BUILTIN AGDATCMQUOTEOMEGATERM             quoteωTC                   #-}
{-# BUILTIN AGDATCMGETCONTEXT                 getContext                 #-}
{-# BUILTIN AGDATCMEXTENDCONTEXT              extendContext              #-}
{-# BUILTIN AGDATCMINCONTEXT                  inContext                  #-}
{-# BUILTIN AGDATCMFRESHNAME                  freshName                  #-}
{-# BUILTIN AGDATCMDECLAREDEF                 declareDef                 #-}
{-# BUILTIN AGDATCMDECLAREPOSTULATE           declarePostulate           #-}
{-# BUILTIN AGDATCMDECLAREDATA                declareData                #-}
{-# BUILTIN AGDATCMDEFINEDATA                 defineData                 #-}
{-# BUILTIN AGDATCMDEFINEFUN                  defineFun                  #-}
{-# BUILTIN AGDATCMGETTYPE                    getType                    #-}
{-# BUILTIN AGDATCMGETDEFINITION              getDefinition              #-}
{-# BUILTIN AGDATCMBLOCK                      blockTC                    #-}
{-# BUILTIN AGDATCMCOMMIT                     commitTC                   #-}
{-# BUILTIN AGDATCMISMACRO                    isMacro                    #-}
{-# BUILTIN AGDATCMPRAGMAFOREIGN              pragmaForeign              #-}
{-# BUILTIN AGDATCMPRAGMACOMPILE              pragmaCompile              #-}
{-# BUILTIN AGDATCMWITHNORMALISATION          withNormalisation          #-}
{-# BUILTIN AGDATCMWITHRECONSTRUCTED          withReconstructed          #-}
{-# BUILTIN AGDATCMWITHEXPANDLAST             withExpandLast             #-}
{-# BUILTIN AGDATCMWITHREDUCEDEFS             withReduceDefs             #-}
{-# BUILTIN AGDATCMASKNORMALISATION           askNormalisation           #-}
{-# BUILTIN AGDATCMASKRECONSTRUCTED           askReconstructed           #-}
{-# BUILTIN AGDATCMASKEXPANDLAST              askExpandLast              #-}
{-# BUILTIN AGDATCMASKREDUCEDEFS              askReduceDefs              #-}
{-# BUILTIN AGDATCMFORMATERRORPARTS           formatErrorParts           #-}
{-# BUILTIN AGDATCMDEBUGPRINT                 debugPrint                 #-}
{-# BUILTIN AGDATCMNOCONSTRAINTS              noConstraints              #-}
{-# BUILTIN AGDATCMRUNSPECULATIVE             runSpeculative             #-}
{-# BUILTIN AGDATCMGETINSTANCES               getInstances               #-}

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
{-# COMPILE JS blockTC           = _ => _ =>           undefined #-}
{-# COMPILE JS commitTC          =                     undefined #-}
{-# COMPILE JS isMacro           = _ =>                undefined #-}
{-# COMPILE JS pragmaForeign     = _ => _ =>           undefined #-}
{-# COMPILE JS pragmaCompile     = _ => _ => _ =>      undefined #-}
{-# COMPILE JS withNormalisation = _ => _ => _ => _ => undefined #-}
{-# COMPILE JS withReconstructed = _ => _ => _ => _ => undefined #-}
{-# COMPILE JS withExpandLast    = _ => _ => _ => _ => undefined #-}
{-# COMPILE JS withReduceDefs    = _ => _ => _ => _ => undefined #-}
{-# COMPILE JS askNormalisation  =                     undefined #-}
{-# COMPILE JS askReconstructed  =                     undefined #-}
{-# COMPILE JS askExpandLast     =                     undefined #-}
{-# COMPILE JS askReduceDefs     =                     undefined #-}
{-# COMPILE JS debugPrint        = _ => _ => _ =>      undefined #-}
{-# COMPILE JS noConstraints     = _ => _ => _ =>      undefined #-}
{-# COMPILE JS runSpeculative    = _ => _ => _ =>      undefined #-}
{-# COMPILE JS getInstances      = _ =>                undefined #-}

private
  filter : (Name → Bool) → List Name → List Name
  filter p [] = []
  filter p (x ∷ xs) with p x
  ... | true  = x ∷ filter p xs
  ... | false = filter p xs

  _∈_ : Name → List Name → Bool
  n ∈ []      = false
  n ∈ (n' ∷ l) with primQNameEquality n n'
  ... | true  = true
  ... | false = n ∈ l

  _∉_ : Name → List Name → Bool
  n ∉ l with n ∈ l
  ... | true  = false
  ... | false = true

  _++_ : List Name → List Name → List Name
  [] ++ l       = l
  (x ∷ xs) ++ l = x ∷ (xs ++ l)

  combineReduceDefs : (Σ Bool λ _ → List Name) → (Σ Bool λ _ → List Name) → (Σ Bool λ _ → List Name)
  combineReduceDefs (true  , defs₁) (true  , defs₂) = (true  , filter (_∈ defs₁) defs₂)
  combineReduceDefs (false , defs₁) (true  , defs₂) = (true  , filter (_∉ defs₁) defs₂)
  combineReduceDefs (true  , defs₁) (false , defs₂) = (true  , filter (_∉ defs₂) defs₁)
  combineReduceDefs (false , defs₁) (false , defs₂) = (false , defs₁ ++ defs₂)

onlyReduceDefs dontReduceDefs : ∀ {a} {A : Set a} → List Name → TC A → TC A
onlyReduceDefs defs x = bindTC askReduceDefs (λ exDefs → withReduceDefs (combineReduceDefs (true  , defs) exDefs) x)
dontReduceDefs defs x = bindTC askReduceDefs (λ exDefs → withReduceDefs (combineReduceDefs (false , defs) exDefs) x)

blockOnMeta   : ∀ {a} {A : Set a} → Meta → TC A
blockOnMeta m = blockTC (blockerMeta m)

{-# WARNING_ON_USAGE onlyReduceDefs "DEPRECATED: Use `withReduceDefs` instead of `onlyReduceDefs`" #-}
{-# WARNING_ON_USAGE dontReduceDefs "DEPRECATED: Use `withReduceDefs` instead of `dontReduceDefs`" #-}
