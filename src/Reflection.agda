------------------------------------------------------------------------
-- The Agda standard library
--
-- Support for reflection
------------------------------------------------------------------------

module Reflection where

open import Data.Bool as Bool using (Bool); open Bool.Bool
open import Data.List using (List); open Data.List.List
open import Data.Nat using (ℕ) renaming (_≟_ to _≟-ℕ_)
open import Data.Float using (Float) renaming (_≟_ to _≟f_)
open import Data.Char using (Char) renaming (_≟_ to _≟c_)
open import Data.String using (String) renaming (_≟_ to _≟s_)
open import Data.Product
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.TrustMe
open import Relation.Nullary
open import Relation.Nullary.Decidable as Dec
open import Relation.Nullary.Product

------------------------------------------------------------------------
-- Names

-- Names.

postulate Name : Set

{-# BUILTIN QNAME Name #-}

private
  primitive
    primQNameEquality : Name → Name → Bool

-- Equality of names is decidable.

infix 4 _==_ _≟-Name_

private

  _==_ : Name → Name → Bool
  _==_ = primQNameEquality

_≟-Name_ : Decidable {A = Name} _≡_
s₁ ≟-Name s₂ with s₁ == s₂
... | true  = yes trustMe
... | false = no whatever
  where postulate whatever : _

------------------------------------------------------------------------
-- Terms

-- Is the argument visible (explicit), hidden (implicit), or an
-- instance argument?

data Visibility : Set where
  visible hidden instance : Visibility

{-# BUILTIN HIDING   Visibility #-}
{-# BUILTIN VISIBLE  visible    #-}
{-# BUILTIN HIDDEN   hidden     #-}
{-# BUILTIN INSTANCE instance   #-}

-- Arguments can be relevant or irrelevant.

data Relevance : Set where
  relevant irrelevant : Relevance

{-# BUILTIN RELEVANCE  Relevance  #-}
{-# BUILTIN RELEVANT   relevant   #-}
{-# BUILTIN IRRELEVANT irrelevant #-}

-- Arguments.

data Arg-info : Set where
  arg-info : (v : Visibility) (r : Relevance) → Arg-info

data Arg (A : Set) : Set where
  arg : (i : Arg-info) (x : A) → Arg A

{-# BUILTIN ARGINFO    Arg-info #-}
{-# BUILTIN ARGARGINFO arg-info #-}
{-# BUILTIN ARG        Arg      #-}
{-# BUILTIN ARGARG     arg      #-}

-- Literals.

data Literal : Set where
  nat    : ℕ → Literal
  float  : Float → Literal
  char   : Char → Literal
  string : String → Literal
  name   : Name → Literal

{-# BUILTIN AGDALITERAL   Literal #-}
{-# BUILTIN AGDALITNAT    nat #-}
{-# BUILTIN AGDALITFLOAT  float #-}
{-# BUILTIN AGDALITCHAR   char #-}
{-# BUILTIN AGDALITSTRING string #-}
{-# BUILTIN AGDALITQNAME  name #-}

-- Terms.

mutual
  data Term : Set where
    -- Variable applied to arguments.
    var     : (x : ℕ) (args : List (Arg Term)) → Term
    -- Constructor applied to arguments.
    con     : (c : Name) (args : List (Arg Term)) → Term
    -- Identifier applied to arguments.
    def     : (f : Name) (args : List (Arg Term)) → Term
    -- Different kinds of λ-abstraction.
    lam     : (v : Visibility) (t : Term) → Term
    -- Pi-type.
    pi      : (t₁ : Arg Type) (t₂ : Type) → Term
    -- A sort.
    sort    : Sort → Term
    -- A literal.
    lit     : Literal → Term
    -- Anything else.
    unknown : Term

  data Type : Set where
    el : (s : Sort) (t : Term) → Type

  data Sort : Set where
    -- A Set of a given (possibly neutral) level.
    set     : (t : Term) → Sort
    -- A Set of a given concrete level.
    lit     : (n : ℕ) → Sort
    -- Anything else.
    unknown : Sort

{-# BUILTIN AGDASORT            Sort    #-}
{-# BUILTIN AGDATYPE            Type    #-}
{-# BUILTIN AGDATERM            Term    #-}
{-# BUILTIN AGDATERMVAR         var     #-}
{-# BUILTIN AGDATERMCON         con     #-}
{-# BUILTIN AGDATERMDEF         def     #-}
{-# BUILTIN AGDATERMLAM         lam     #-}
{-# BUILTIN AGDATERMPI          pi      #-}
{-# BUILTIN AGDATERMSORT        sort    #-}
{-# BUILTIN AGDATERMLIT         lit     #-}
{-# BUILTIN AGDATERMUNSUPPORTED unknown #-}
{-# BUILTIN AGDATYPEEL          el      #-}
{-# BUILTIN AGDASORTSET         set     #-}
{-# BUILTIN AGDASORTLIT         lit     #-}
{-# BUILTIN AGDASORTUNSUPPORTED unknown #-}

------------------------------------------------------------------------
-- Definitions

data Pattern : Set where
  con  : Name → List (Arg Pattern) → Pattern
  dot  : Pattern
  var  : Pattern
  lit  : Literal → Pattern
  proj : Name → Pattern

{-# BUILTIN AGDAPATTERN Pattern #-}
{-# BUILTIN AGDAPATCON con #-}
{-# BUILTIN AGDAPATDOT dot #-}
{-# BUILTIN AGDAPATVAR var #-}
{-# BUILTIN AGDAPATLIT lit #-}
{-# BUILTIN AGDAPATPROJ proj #-}

data Clause : Set where
  clause : List (Arg Pattern) → Term → Clause

{-# BUILTIN AGDACLAUSE Clause #-}
{-# BUILTIN AGDACLAUSECON clause #-}

-- Function definition.
data FunctionDef : Set where
  fun-def : Type → List Clause → FunctionDef

{-# BUILTIN AGDAFUNDEF    FunctionDef #-}
{-# BUILTIN AGDAFUNDEFCON fun-def     #-}

postulate
  -- Data type definition.
  Data-type : Set
  -- Record type definition.
  Record    : Set

{-# BUILTIN AGDADATADEF   Data-type #-}
{-# BUILTIN AGDARECORDDEF Record    #-}

-- Definitions.

data Definition : Set where
  function     : FunctionDef  → Definition
  data-type    : Data-type → Definition
  record′      : Record    → Definition
  constructor′ : Definition
  axiom        : Definition
  primitive′   : Definition

{-# BUILTIN AGDADEFINITION                Definition   #-}
{-# BUILTIN AGDADEFINITIONFUNDEF          function     #-}
{-# BUILTIN AGDADEFINITIONDATADEF         data-type    #-}
{-# BUILTIN AGDADEFINITIONRECORDDEF       record′      #-}
{-# BUILTIN AGDADEFINITIONDATACONSTRUCTOR constructor′ #-}
{-# BUILTIN AGDADEFINITIONPOSTULATE       axiom        #-}
{-# BUILTIN AGDADEFINITIONPRIMITIVE       primitive′   #-}

private
  primitive
    primQNameType        : Name → Type
    primQNameDefinition  : Name → Definition
    primDataConstructors : Data-type → List Name

-- The type of the thing with the given name.

type : Name → Type
type = primQNameType

-- The definition of the thing with the given name.

definition : Name → Definition
definition = primQNameDefinition

-- The constructors of the given data type.

constructors : Data-type → List Name
constructors = primDataConstructors

------------------------------------------------------------------------
-- Term equality is decidable

-- Boring helper functions.

private

  cong₂′ : ∀ {A B C : Set} (f : A → B → C) {x y u v} →
          x ≡ y × u ≡ v → f x u ≡ f y v
  cong₂′ f = uncurry (cong₂ f)

  cong₃′ : ∀ {A B C D : Set} (f : A → B → C → D) {x y u v r s} →
           x ≡ y × u ≡ v × r ≡ s → f x u r ≡ f y v s
  cong₃′ f (refl , refl , refl) = refl

  arg₁ : ∀ {A i i′} {x x′ : A} → arg i x ≡ arg i′ x′ → i ≡ i′
  arg₁ refl = refl

  arg₂ : ∀ {A i i′} {x x′ : A} → arg i x ≡ arg i′ x′ → x ≡ x′
  arg₂ refl = refl

  arg-info₁ : ∀ {v v′ r r′} → arg-info v r ≡ arg-info v′ r′ → v ≡ v′
  arg-info₁ refl = refl

  arg-info₂ : ∀ {v v′ r r′} → arg-info v r ≡ arg-info v′ r′ → r ≡ r′
  arg-info₂ refl = refl

  cons₁ : ∀ {A : Set} {x y} {xs ys : List A} → x ∷ xs ≡ y ∷ ys → x ≡ y
  cons₁ refl = refl

  cons₂ : ∀ {A : Set} {x y} {xs ys : List A} → x ∷ xs ≡ y ∷ ys → xs ≡ ys
  cons₂ refl = refl

  var₁ : ∀ {x x′ args args′} → Term.var x args ≡ var x′ args′ → x ≡ x′
  var₁ refl = refl

  var₂ : ∀ {x x′ args args′} → Term.var x args ≡ var x′ args′ → args ≡ args′
  var₂ refl = refl

  con₁ : ∀ {c c′ args args′} → Term.con c args ≡ con c′ args′ → c ≡ c′
  con₁ refl = refl

  con₂ : ∀ {c c′ args args′} → Term.con c args ≡ con c′ args′ → args ≡ args′
  con₂ refl = refl

  def₁ : ∀ {f f′ args args′} → def f args ≡ def f′ args′ → f ≡ f′
  def₁ refl = refl

  def₂ : ∀ {f f′ args args′} → def f args ≡ def f′ args′ → args ≡ args′
  def₂ refl = refl

  lam₁ : ∀ {v v′ t t′} → lam v t ≡ lam v′ t′ → v ≡ v′
  lam₁ refl = refl

  lam₂ : ∀ {v v′ t t′} → lam v t ≡ lam v′ t′ → t ≡ t′
  lam₂ refl = refl

  pi₁ : ∀ {t₁ t₁′ t₂ t₂′} → pi t₁ t₂ ≡ pi t₁′ t₂′ → t₁ ≡ t₁′
  pi₁ refl = refl

  pi₂ : ∀ {t₁ t₁′ t₂ t₂′} → pi t₁ t₂ ≡ pi t₁′ t₂′ → t₂ ≡ t₂′
  pi₂ refl = refl

  sort₁ : ∀ {x y} → sort x ≡ sort y → x ≡ y
  sort₁ refl = refl

  lit₁ : ∀ {x y} → Term.lit x ≡ lit y → x ≡ y
  lit₁ refl = refl

  set₁ : ∀ {x y} → set x ≡ set y → x ≡ y
  set₁ refl = refl

  slit₁ : ∀ {x y} → Sort.lit x ≡ lit y → x ≡ y
  slit₁ refl = refl

  el₁ : ∀ {s s′ t t′} → el s t ≡ el s′ t′ → s ≡ s′
  el₁ refl = refl

  el₂ : ∀ {s s′ t t′} → el s t ≡ el s′ t′ → t ≡ t′
  el₂ refl = refl

  nat₁ : ∀ {x y} → nat x ≡ nat y → x ≡ y
  nat₁ refl = refl

  float₁ : ∀ {x y} → float x ≡ float y → x ≡ y
  float₁ refl = refl

  char₁ : ∀ {x y} → char x ≡ char y → x ≡ y
  char₁ refl = refl

  string₁ : ∀ {x y} → string x ≡ string y → x ≡ y
  string₁ refl = refl

  name₁ : ∀ {x y} → name x ≡ name y → x ≡ y
  name₁ refl = refl

_≟-Visibility_ : Decidable (_≡_ {A = Visibility})
visible  ≟-Visibility visible  = yes refl
hidden   ≟-Visibility hidden   = yes refl
instance ≟-Visibility instance = yes refl
visible  ≟-Visibility hidden   = no λ()
visible  ≟-Visibility instance = no λ()
hidden   ≟-Visibility visible  = no λ()
hidden   ≟-Visibility instance = no λ()
instance ≟-Visibility visible  = no λ()
instance ≟-Visibility hidden   = no λ()

_≟-Relevance_ : Decidable (_≡_ {A = Relevance})
relevant   ≟-Relevance relevant   = yes refl
irrelevant ≟-Relevance irrelevant = yes refl
relevant   ≟-Relevance irrelevant = no λ()
irrelevant ≟-Relevance relevant   = no λ()

_≟-Arg-info_ : Decidable (_≡_ {A = Arg-info})
arg-info v r ≟-Arg-info arg-info v′ r′ =
  Dec.map′ (cong₂′ arg-info)
           < arg-info₁ , arg-info₂ >
           (v ≟-Visibility v′ ×-dec r ≟-Relevance r′)

_≟-Lit_ : Decidable (_≡_ {A = Literal})
nat x ≟-Lit nat x₁ = Dec.map′ (cong nat) nat₁ (x ≟-ℕ x₁)
nat x ≟-Lit float x₁ = no (λ ())
nat x ≟-Lit char x₁ = no (λ ())
nat x ≟-Lit string x₁ = no (λ ())
nat x ≟-Lit name x₁ = no (λ ())
float x ≟-Lit nat x₁ = no (λ ())
float x ≟-Lit float x₁ = Dec.map′ (cong float) float₁ (x ≟f x₁)
float x ≟-Lit char x₁ = no (λ ())
float x ≟-Lit string x₁ = no (λ ())
float x ≟-Lit name x₁ = no (λ ())
char x ≟-Lit nat x₁ = no (λ ())
char x ≟-Lit float x₁ = no (λ ())
char x ≟-Lit char x₁ = Dec.map′ (cong char) char₁ (x ≟c x₁)
char x ≟-Lit string x₁ = no (λ ())
char x ≟-Lit name x₁ = no (λ ())
string x ≟-Lit nat x₁ = no (λ ())
string x ≟-Lit float x₁ = no (λ ())
string x ≟-Lit char x₁ = no (λ ())
string x ≟-Lit string x₁ = Dec.map′ (cong string) string₁ (x ≟s x₁)
string x ≟-Lit name x₁ = no (λ ())
name x ≟-Lit nat x₁ = no (λ ())
name x ≟-Lit float x₁ = no (λ ())
name x ≟-Lit char x₁ = no (λ ())
name x ≟-Lit string x₁ = no (λ ())
name x ≟-Lit name x₁ = Dec.map′ (cong name) name₁ (x ≟-Name x₁)

mutual
  infix 4 _≟_ _≟-Args_ _≟-ArgType_

  _≟-ArgTerm_ : Decidable (_≡_ {A = Arg Term})
  arg i a ≟-ArgTerm arg i′ a′ =
    Dec.map′ (cong₂′ arg)
             < arg₁ , arg₂ >
             (i ≟-Arg-info i′ ×-dec a ≟ a′)

  _≟-ArgType_ : Decidable (_≡_ {A = Arg Type})
  arg i a ≟-ArgType arg i′ a′ =
    Dec.map′ (cong₂′ arg)
             < arg₁ , arg₂ >
             (i ≟-Arg-info i′ ×-dec a ≟-Type a′)

  _≟-Args_ : Decidable (_≡_ {A = List (Arg Term)})
  []       ≟-Args []       = yes refl
  (x ∷ xs) ≟-Args (y ∷ ys) = Dec.map′ (cong₂′ _∷_) < cons₁ , cons₂ > (x ≟-ArgTerm y ×-dec xs ≟-Args ys)
  []       ≟-Args (_ ∷ _)  = no λ()
  (_ ∷ _)  ≟-Args []       = no λ()

  _≟_ : Decidable (_≡_ {A = Term})
  var x args ≟ var x′ args′ = Dec.map′ (cong₂′ var) < var₁ , var₂ > (x ≟-ℕ x′          ×-dec args ≟-Args args′)
  con c args ≟ con c′ args′ = Dec.map′ (cong₂′ con) < con₁ , con₂ > (c ≟-Name c′       ×-dec args ≟-Args args′)
  def f args ≟ def f′ args′ = Dec.map′ (cong₂′ def) < def₁ , def₂ > (f ≟-Name f′       ×-dec args ≟-Args args′)
  lam v t    ≟ lam v′ t′    = Dec.map′ (cong₂′ lam) < lam₁ , lam₂ > (v ≟-Visibility v′ ×-dec t ≟ t′)
  pi t₁ t₂   ≟ pi t₁′ t₂′   = Dec.map′ (cong₂′ pi)  < pi₁  , pi₂  > (t₁ ≟-ArgType t₁′  ×-dec t₂ ≟-Type t₂′)
  sort s     ≟ sort s′      = Dec.map′ (cong sort)  sort₁           (s ≟-Sort s′)
  lit l      ≟ lit l′       = Dec.map′ (cong lit)   lit₁           (l ≟-Lit l′)
  unknown    ≟ unknown      = yes refl

  var x args ≟ con c args′ = no λ()
  var x args ≟ def f args′ = no λ()
  var x args ≟ lam v t     = no λ()
  var x args ≟ pi t₁ t₂    = no λ()
  var x args ≟ sort _      = no λ()
  var x args ≟ lit _      = no λ()
  var x args ≟ unknown     = no λ()
  con c args ≟ var x args′ = no λ()
  con c args ≟ def f args′ = no λ()
  con c args ≟ lam v t     = no λ()
  con c args ≟ pi t₁ t₂    = no λ()
  con c args ≟ sort _      = no λ()
  con c args ≟ lit _      = no λ()
  con c args ≟ unknown     = no λ()
  def f args ≟ var x args′ = no λ()
  def f args ≟ con c args′ = no λ()
  def f args ≟ lam v t     = no λ()
  def f args ≟ pi t₁ t₂    = no λ()
  def f args ≟ sort _      = no λ()
  def f args ≟ lit _      = no λ()
  def f args ≟ unknown     = no λ()
  lam v t    ≟ var x args  = no λ()
  lam v t    ≟ con c args  = no λ()
  lam v t    ≟ def f args  = no λ()
  lam v t    ≟ pi t₁ t₂    = no λ()
  lam v t    ≟ sort _      = no λ()
  lam v t    ≟ lit _      = no λ()
  lam v t    ≟ unknown     = no λ()
  pi t₁ t₂   ≟ var x args  = no λ()
  pi t₁ t₂   ≟ con c args  = no λ()
  pi t₁ t₂   ≟ def f args  = no λ()
  pi t₁ t₂   ≟ lam v t     = no λ()
  pi t₁ t₂   ≟ sort _      = no λ()
  pi t₁ t₂   ≟ lit _      = no λ()
  pi t₁ t₂   ≟ unknown     = no λ()
  sort _     ≟ var x args  = no λ()
  sort _     ≟ con c args  = no λ()
  sort _     ≟ def f args  = no λ()
  sort _     ≟ lam v t     = no λ()
  sort _     ≟ pi t₁ t₂    = no λ()
  sort _     ≟ lit _       = no λ()
  sort _     ≟ unknown     = no λ()
  lit _     ≟ var x args  = no λ()
  lit _     ≟ con c args  = no λ()
  lit _     ≟ def f args  = no λ()
  lit _     ≟ lam v t     = no λ()
  lit _     ≟ pi t₁ t₂    = no λ()
  lit _     ≟ sort _      = no λ()
  lit _     ≟ unknown     = no λ()
  unknown    ≟ var x args  = no λ()
  unknown    ≟ con c args  = no λ()
  unknown    ≟ def f args  = no λ()
  unknown    ≟ lam v t     = no λ()
  unknown    ≟ pi t₁ t₂    = no λ()
  unknown    ≟ sort _      = no λ()
  unknown    ≟ lit _       = no λ()

  _≟-Type_ : Decidable (_≡_ {A = Type})
  el s t ≟-Type el s′ t′ = Dec.map′ (cong₂′ el) < el₁ , el₂ > (s ≟-Sort s′ ×-dec t ≟ t′)

  _≟-Sort_ : Decidable (_≡_ {A = Sort})
  set t   ≟-Sort set t′  = Dec.map′ (cong set) set₁ (t ≟ t′)
  lit n   ≟-Sort lit n′  = Dec.map′ (cong lit) slit₁ (n ≟-ℕ n′)
  unknown ≟-Sort unknown = yes refl
  set _   ≟-Sort lit _   = no λ()
  set _   ≟-Sort unknown = no λ()
  lit _   ≟-Sort set _   = no λ()
  lit _   ≟-Sort unknown = no λ()
  unknown ≟-Sort set _   = no λ()
  unknown ≟-Sort lit _   = no λ()
