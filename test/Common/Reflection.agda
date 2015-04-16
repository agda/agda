
module Common.Reflection where

open import Common.Level
open import Common.Prelude renaming (Nat to ℕ)

postulate QName : Set
{-# BUILTIN QNAME QName #-}
primitive primQNameEquality : QName → QName → Bool
primitive primQNameLess : QName → QName → Bool

data Hiding : Set where
  hidden visible inst : Hiding

{-# BUILTIN HIDING   Hiding   #-}
{-# BUILTIN HIDDEN   hidden   #-}
{-# BUILTIN VISIBLE  visible  #-}
{-# BUILTIN INSTANCE inst     #-}

-- relevant    the argument is (possibly) relevant at compile-time
-- irrelevant  the argument is irrelevant at compile- and runtime
data Relevance : Set where
  relevant irrelevant : Relevance

{-# BUILTIN RELEVANCE  Relevance  #-}
{-# BUILTIN RELEVANT   relevant   #-}
{-# BUILTIN IRRELEVANT irrelevant #-}

data ArgInfo : Set where
  argInfo : Hiding → Relevance → ArgInfo

data Arg A : Set where
  arg : ArgInfo → A → Arg A

{-# BUILTIN ARGINFO    ArgInfo #-}
{-# BUILTIN ARG        Arg     #-}
{-# BUILTIN ARGARG     arg     #-}
{-# BUILTIN ARGARGINFO argInfo #-}

data Abs (A : Set) : Set where
  -- The String here is just a hint to help display the variable.
  -- The actual binding structure is with de Bruijn indices.
  abs : (s : String) (x : A) → Abs A

{-# BUILTIN ABS    Abs #-}
{-# BUILTIN ABSABS abs #-}

data Literal : Set where
  nat    : ℕ → Literal
  float  : Float → Literal
  char   : Char → Literal
  string : String → Literal
  qname  : QName → Literal

{-# BUILTIN AGDALITERAL   Literal #-}
{-# BUILTIN AGDALITNAT    nat     #-}
{-# BUILTIN AGDALITFLOAT  float   #-}
{-# BUILTIN AGDALITCHAR   char    #-}
{-# BUILTIN AGDALITSTRING string  #-}
{-# BUILTIN AGDALITQNAME  qname   #-}

Args : Set

data Type : Set
data Sort : Set
data Clause : Set

data Term : Set where
  var           : ℕ → Args → Term
  con           : QName → Args → Term
  def           : QName → Args → Term
  lam           : Hiding → Abs Term → Term
  extLam        : List Clause → Args → Term
  pi            : Arg Type → Abs Type → Term
  sort          : Sort → Term
  lit           : Literal → Term
  quote-term    : Term → Term
  quote-goal    : Abs Term → Term
  quote-context : Term
  unquote-term  : Term → Args → Term
  unknown       : Term

Args = List (Arg Term)

data Type where
  el : Sort → Term → Type

data Sort where
  set     : Term → Sort
  lit     : ℕ → Sort
  unknown : Sort

data Pattern : Set where
  con    : QName → List (Arg Pattern) → Pattern
  dot    : Pattern
  var    : String → Pattern
  lit    : Literal → Pattern
  absurd : Pattern
  projP  : QName → Pattern

data Clause where
  clause       : List (Arg Pattern) → Term → Clause
  absurdClause : List (Arg Pattern) → Clause

{-# BUILTIN AGDASORT            Sort    #-}
{-# BUILTIN AGDATERM            Term    #-}
{-# BUILTIN AGDATYPE            Type    #-}
{-# BUILTIN AGDAPATTERN         Pattern #-}
{-# BUILTIN AGDACLAUSE          Clause  #-}

{-# BUILTIN AGDATERMVAR         var     #-}
{-# BUILTIN AGDATERMCON         con     #-}
{-# BUILTIN AGDATERMDEF         def     #-}
{-# BUILTIN AGDATERMLAM         lam     #-}
{-# BUILTIN AGDATERMEXTLAM      extLam  #-}
{-# BUILTIN AGDATERMPI          pi      #-}
{-# BUILTIN AGDATERMSORT        sort    #-}
{-# BUILTIN AGDATERMLIT         lit     #-}
{-# BUILTIN AGDATERMQUOTETERM    quote-term    #-}
{-# BUILTIN AGDATERMQUOTEGOAL    quote-goal    #-}
{-# BUILTIN AGDATERMQUOTECONTEXT quote-context #-}
{-# BUILTIN AGDATERMUNQUOTE      unquote-term  #-}
{-# BUILTIN AGDATERMUNSUPPORTED unknown #-}
{-# BUILTIN AGDATYPEEL          el      #-}
{-# BUILTIN AGDASORTSET         set     #-}
{-# BUILTIN AGDASORTLIT         lit     #-}
{-# BUILTIN AGDASORTUNSUPPORTED unknown #-}

{-# BUILTIN AGDAPATCON    con    #-}
{-# BUILTIN AGDAPATDOT    dot    #-}
{-# BUILTIN AGDAPATVAR    var    #-}
{-# BUILTIN AGDAPATLIT    lit    #-}
{-# BUILTIN AGDAPATABSURD absurd #-}
{-# BUILTIN AGDAPATPROJ   projP  #-}

{-# BUILTIN AGDACLAUSECLAUSE clause       #-}
{-# BUILTIN AGDACLAUSEABSURD absurdClause #-}

data FunDef : Set where
  funDef : Type → List Clause → FunDef

{-# BUILTIN AGDAFUNDEF    FunDef #-}
{-# BUILTIN AGDAFUNDEFCON funDef #-}

postulate
  DataDef   : Set
  RecordDef : Set

{-# BUILTIN AGDADATADEF   DataDef   #-}
{-# BUILTIN AGDARECORDDEF RecordDef #-}

data Definition : Set where
  funDef          : FunDef    → Definition
  dataDef         : DataDef   → Definition
  recordDef       : RecordDef → Definition
  dataConstructor : Definition
  axiom           : Definition
  prim            : Definition

{-# BUILTIN AGDADEFINITION                Definition      #-}
{-# BUILTIN AGDADEFINITIONFUNDEF          funDef          #-}
{-# BUILTIN AGDADEFINITIONDATADEF         dataDef         #-}
{-# BUILTIN AGDADEFINITIONRECORDDEF       recordDef       #-}
{-# BUILTIN AGDADEFINITIONDATACONSTRUCTOR dataConstructor #-}
{-# BUILTIN AGDADEFINITIONPOSTULATE       axiom           #-}
{-# BUILTIN AGDADEFINITIONPRIMITIVE       prim            #-}

primitive
  primQNameType              : QName → Type
  primQNameDefinition        : QName → Definition
  primDataNumberOfParameters : DataDef → ℕ
  primDataConstructors       : DataDef   → List QName
--primRecordConstructor      : RecordDef → QName
--primRecordFields           : RecordDef → List QName

type : QName → Type
type = primQNameType
