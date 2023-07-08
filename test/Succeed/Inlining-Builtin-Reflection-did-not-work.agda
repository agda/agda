
module _ where

open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Word
open import Agda.Builtin.List
open import Agda.Builtin.String
open import Agda.Builtin.Char
open import Agda.Builtin.Float
open import Agda.Builtin.Sigma

-- Names --

postulate Name : Set
{-# BUILTIN QNAME Name #-}

primitive
  primQNameEquality : Name → Name → Bool
  primQNameLess     : Name → Name → Bool
  primShowQName     : Name → String

-- Metavariables --

postulate Meta : Set
{-# BUILTIN AGDAMETA Meta #-}

primitive
  primMetaEquality : Meta → Meta → Bool
  primMetaLess     : Meta → Meta → Bool
  primShowMeta     : Meta → String

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

data Arg (A : Set) : Set where
  arg : (i : ArgInfo) (x : A) → Arg A

{-# BUILTIN ARGINFO    ArgInfo  #-}
{-# BUILTIN ARGARGINFO arg-info #-}
{-# BUILTIN ARG        Arg      #-}
{-# BUILTIN ARGARG     arg      #-}

-- Name abstraction --

data Abs (A : Set) : Set where
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

-- Patterns --


-- Terms --

data Sort   : Set
data Clause : Set
data Term   : Set
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

data Pattern : Set where
  con    : (c : Name) (ps : List (Arg Pattern)) → Pattern
  dot    : (t : Term)    → Pattern
  var    : (x : Nat)     → Pattern
  lit    : (l : Literal) → Pattern
  proj   : (f : Name)    → Pattern
  absurd : (x : Nat)     → Pattern

data Clause where
  clause        : (tel : Telescope) (ps : List (Arg Pattern)) (t : Term) → Clause
  absurd-clause : (tel : Telescope) (ps : List (Arg Pattern)) → Clause

{-# BUILTIN AGDATERM    Term    #-}
{-# BUILTIN AGDASORT    Sort    #-}
{-# BUILTIN AGDAPATTERN Pattern #-}
{-# BUILTIN AGDACLAUSE  Clause  #-}

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
  TC            : ∀ {a} → Set a → Set a
  returnTC      : ∀ {a} {A : Set a} → A → TC A
  bindTC        : ∀ {a b} {A : Set a} {B : Set b} → TC A → (A → TC B) → TC B
  unify         : Term → Term → TC ⊤
  typeError     : ∀ {a} {A : Set a} → List ErrorPart → TC A
  inferType     : Term → TC Type
  checkType     : Term → Type → TC Term
  normalise     : Term → TC Term
  catchTC       : ∀ {a} {A : Set a} → TC A → TC A → TC A
  quoteTC       : ∀ {a} {A : Set a} → A → TC Term
  unquoteTC     : ∀ {a} {A : Set a} → Term → TC A
  getContext    : TC Telescope
  extendContext : ∀ {a} {A : Set a} → String → Arg Type → TC A → TC A
  inContext     : ∀ {a} {A : Set a} → Telescope → TC A → TC A
  freshName     : String → TC Name
  declareDef    : Arg Name → Type → TC ⊤
  defineFun     : Name → List Clause → TC ⊤
  getType       : Name → TC Type
  getDefinition : Name → TC Definition
  commitTC      : TC ⊤

{-# BUILTIN AGDATCM              TC            #-}
{-# BUILTIN AGDATCMRETURN        returnTC      #-}
{-# BUILTIN AGDATCMBIND          bindTC        #-}
{-# BUILTIN AGDATCMUNIFY         unify         #-}
{-# BUILTIN AGDATCMTYPEERROR     typeError     #-}
{-# BUILTIN AGDATCMINFERTYPE     inferType     #-}
{-# BUILTIN AGDATCMCHECKTYPE     checkType     #-}
{-# BUILTIN AGDATCMNORMALISE     normalise     #-}
{-# BUILTIN AGDATCMCATCHERROR    catchTC       #-}
{-# BUILTIN AGDATCMQUOTETERM     quoteTC       #-}
{-# BUILTIN AGDATCMUNQUOTETERM   unquoteTC     #-}
{-# BUILTIN AGDATCMGETCONTEXT    getContext    #-}
{-# BUILTIN AGDATCMEXTENDCONTEXT extendContext #-}
{-# BUILTIN AGDATCMINCONTEXT     inContext     #-}
{-# BUILTIN AGDATCMFRESHNAME     freshName     #-}
{-# BUILTIN AGDATCMDECLAREDEF    declareDef    #-}
{-# BUILTIN AGDATCMDEFINEFUN     defineFun     #-}
{-# BUILTIN AGDATCMGETTYPE       getType       #-}
{-# BUILTIN AGDATCMGETDEFINITION getDefinition #-}
{-# BUILTIN AGDATCMCOMMIT        commitTC      #-}

-- The code below used to be rejected, but it was accepted if the code
-- above was placed in a separate module.

postulate
  A : Set
  a : A
  done : {A : Set} → A

helper : Term → Term → TC ⊤
helper hole (meta m args) =
  bindTC (unify hole (lit (meta m))) λ _ →
  unify (meta m args) (def (quote a) [])
helper _ _ = done

macro
  metaLit : Term → TC ⊤
  metaLit hole =
    bindTC (checkType unknown (def (quote A) [])) (helper hole)

m : Meta
m = metaLit
