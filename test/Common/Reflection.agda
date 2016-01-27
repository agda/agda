
module Common.Reflection where

open import Common.Level
open import Common.Prelude

postulate QName : Set
{-# BUILTIN QNAME QName #-}
primitive primQNameEquality : QName → QName → Bool
primitive primQNameLess : QName → QName → Bool
primitive primShowQName : QName → String

postulate Meta : Set
{-# BUILTIN AGDAMETA Meta #-}
primitive primMetaEquality : Meta → Meta → Bool
primitive primMetaLess : Meta → Meta → Bool
primitive primShowMeta : Meta → String

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

pattern vArg x = arg (argInfo visible relevant) x
pattern hArg x = arg (argInfo hidden  relevant) x
pattern iArg x = arg (argInfo inst    relevant) x

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
  nat    : Nat → Literal
  float  : Float → Literal
  char   : Char → Literal
  string : String → Literal
  qname  : QName → Literal
  meta   : Meta → Literal

{-# BUILTIN AGDALITERAL   Literal #-}
{-# BUILTIN AGDALITNAT    nat     #-}
{-# BUILTIN AGDALITFLOAT  float   #-}
{-# BUILTIN AGDALITCHAR   char    #-}
{-# BUILTIN AGDALITSTRING string  #-}
{-# BUILTIN AGDALITQNAME  qname   #-}
{-# BUILTIN AGDALITMETA   meta    #-}

Args : Set
Type : Set

data Sort : Set
data Clause : Set

data Term : Set where
  var           : Nat → Args → Term
  con           : QName → Args → Term
  def           : QName → Args → Term
  lam           : Hiding → Abs Term → Term
  extLam        : List Clause → Args → Term
  pi            : Arg Type → Abs Type → Term
  sort          : Sort → Term
  lit           : Literal → Term
  meta          : Meta → Args → Term
  unknown       : Term

Args = List (Arg Term)
Type = Term

data Sort where
  set     : Term → Sort
  lit     : Nat → Sort
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
{-# BUILTIN AGDATERMMETA        meta    #-}
{-# BUILTIN AGDATERMUNSUPPORTED unknown #-}
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

data Definition : Set where
  funDef          : List Clause → Definition
  dataDef         : Nat → List QName → Definition
  recordDef       : QName → Definition
  dataConstructor : QName → Definition
  axiom           : Definition
  prim            : Definition

{-# BUILTIN AGDADEFINITION                Definition      #-}
{-# BUILTIN AGDADEFINITIONFUNDEF          funDef          #-}
{-# BUILTIN AGDADEFINITIONDATADEF         dataDef         #-}
{-# BUILTIN AGDADEFINITIONRECORDDEF       recordDef       #-}
{-# BUILTIN AGDADEFINITIONDATACONSTRUCTOR dataConstructor #-}
{-# BUILTIN AGDADEFINITIONPOSTULATE       axiom           #-}
{-# BUILTIN AGDADEFINITIONPRIMITIVE       prim            #-}
