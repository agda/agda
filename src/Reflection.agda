------------------------------------------------------------------------
-- The Agda standard library
--
-- Support for reflection
------------------------------------------------------------------------

module Reflection where

open import Data.Unit.Base using (⊤)
open import Data.Bool.Base using (Bool; false; true)
open import Data.List.Base using (List); open Data.List.Base.List
open import Data.Nat using (ℕ) renaming (_≟_ to _≟-ℕ_)
open import Data.Nat.Show renaming (show to showNat)
open import Data.Float using (Float) renaming (_≟_ to _≟f_; show to showFloat)
open import Data.Char using (Char) renaming (_≟_ to _≟c_; show to showChar)
open import Data.String using (String) renaming (_≟_ to _≟s_; show to showString)
open import Data.Word using (Word64) renaming (_≟_ to _≟w_; toℕ to wordToℕ)
open import Data.Product
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.TrustMe
open import Relation.Nullary hiding (module Dec)
open import Relation.Nullary.Decidable as Dec
open import Relation.Nullary.Product

import Agda.Builtin.Reflection as Builtin

------------------------------------------------------------------------
-- Names

-- Names.

open Builtin public using (Name)

-- Equality of names is decidable.

infix 4 _==_ _≟-Name_

private

  _==_ : Name → Name → Bool
  _==_ = Builtin.primQNameEquality

_≟-Name_ : Decidable {A = Name} _≡_
s₁ ≟-Name s₂ with s₁ == s₂
... | true  = yes trustMe
... | false = no whatever
  where postulate whatever : _

-- Names can be shown.

showName : Name → String
showName = Builtin.primShowQName

------------------------------------------------------------------------
-- Metavariables

-- Metavariables.

open Builtin public using (Meta)

-- Equality of metavariables is decidable.

infix 4 _==-Meta_ _≟-Meta_

private

  _==-Meta_ : Meta → Meta → Bool
  _==-Meta_ = Builtin.primMetaEquality

_≟-Meta_ : Decidable {A = Meta} _≡_
s₁ ≟-Meta s₂ with s₁ ==-Meta s₂
... | true  = yes trustMe
... | false = no whatever
  where postulate whatever : _

-- Metas can be shown.

showMeta : Meta → String
showMeta = Builtin.primShowMeta

------------------------------------------------------------------------
-- Terms

-- Is the argument visible (explicit), hidden (implicit), or an
-- instance argument?
open Builtin public using (Visibility; visible; hidden; instance′)

-- Arguments can be relevant or irrelevant.
open Builtin public using (Relevance; relevant; irrelevant)

-- Arguments.
open Builtin public
  renaming ( ArgInfo to Arg-info )
  using    ( arg-info )

visibility : Arg-info → Visibility
visibility (arg-info v _) = v

relevance : Arg-info → Relevance
relevance (arg-info _ r) = r

open Builtin public using (Arg; arg)
open Builtin public using (Abs; abs)

-- Literals.

open Builtin public using (Literal; nat; word64; float; char; string; name; meta)

-- Patterns.

open Builtin public using (Pattern; con; dot; var; lit; proj; absurd)

-- Terms.

open Builtin public
  using    ( Type; Term; var; con; def; lam; pat-lam; pi; lit; meta; unknown
           ; Sort; set
           ; Clause; clause; absurd-clause )
  renaming ( agda-sort to sort )

Clauses = List Clause

------------------------------------------------------------------------
-- Definitions

open Builtin public
  using    ( Definition
           ; function
           ; data-type
           ; axiom
           )
  renaming ( record-type to record′
           ; data-cons   to constructor′
           ; prim-fun    to primitive′ )

showLiteral : Literal → String
showLiteral (nat x)    = showNat x
showLiteral (word64 x) = showNat (wordToℕ x)
showLiteral (float x)  = showFloat x
showLiteral (char x)   = showChar x
showLiteral (string x) = showString x
showLiteral (name x)   = showName x
showLiteral (meta x)   = showMeta x

------------------------------------------------------------------------
-- Type checking monad

-- Type errors
open Builtin public using (ErrorPart; strErr; termErr; nameErr)

-- The monad
open Builtin public
  using ( TC; returnTC; bindTC; unify; typeError; inferType; checkType
        ; normalise; catchTC; getContext; extendContext; inContext
        ; freshName; declareDef; defineFun; getType; getDefinition
        ; blockOnMeta; quoteTC; unquoteTC )

newMeta : Type → TC Term
newMeta = checkType unknown

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

  abs₁ : ∀ {A i i′} {x x′ : A} → abs i x ≡ abs i′ x′ → i ≡ i′
  abs₁ refl = refl

  abs₂ : ∀ {A i i′} {x x′ : A} → abs i x ≡ abs i′ x′ → x ≡ x′
  abs₂ refl = refl

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

  meta₁ : ∀ {x x′ args args′} → Term.meta x args ≡ meta x′ args′ → x ≡ x′
  meta₁ refl = refl

  meta₂ : ∀ {x x′ args args′} → Term.meta x args ≡ meta x′ args′ → args ≡ args′
  meta₂ refl = refl

  lam₁ : ∀ {v v′ t t′} → lam v t ≡ lam v′ t′ → v ≡ v′
  lam₁ refl = refl

  lam₂ : ∀ {v v′ t t′} → lam v t ≡ lam v′ t′ → t ≡ t′
  lam₂ refl = refl

  pat-lam₁ : ∀ {cs cs′ args args′} → pat-lam cs args ≡ pat-lam cs′ args′ → cs ≡ cs′
  pat-lam₁ refl = refl

  pat-lam₂ : ∀ {cs cs′ args args′} → pat-lam cs args ≡ pat-lam cs′ args′ → args ≡ args′
  pat-lam₂ refl = refl

  pi₁ : ∀ {t₁ t₁′ t₂ t₂′} → pi t₁ t₂ ≡ pi t₁′ t₂′ → t₁ ≡ t₁′
  pi₁ refl = refl

  pi₂ : ∀ {t₁ t₁′ t₂ t₂′} → pi t₁ t₂ ≡ pi t₁′ t₂′ → t₂ ≡ t₂′
  pi₂ refl = refl

  sort₁ : ∀ {x y} → sort x ≡ sort y → x ≡ y
  sort₁ refl = refl

  lit₁ : ∀ {x y} → Term.lit x ≡ lit y → x ≡ y
  lit₁ refl = refl

  pcon₁ : ∀ {c c′ args args′} → Pattern.con c args ≡ con c′ args′ → c ≡ c′
  pcon₁ refl = refl

  pcon₂ : ∀ {c c′ args args′} → Pattern.con c args ≡ con c′ args′ → args ≡ args′
  pcon₂ refl = refl

  pvar : ∀ {x y} → Pattern.var x ≡ var y → x ≡ y
  pvar refl = refl

  plit₁ : ∀ {x y} → Pattern.lit x ≡ lit y → x ≡ y
  plit₁ refl = refl

  pproj₁ : ∀ {x y} → proj x ≡ proj y → x ≡ y
  pproj₁ refl = refl

  set₁ : ∀ {x y} → set x ≡ set y → x ≡ y
  set₁ refl = refl

  slit₁ : ∀ {x y} → Sort.lit x ≡ lit y → x ≡ y
  slit₁ refl = refl

  nat₁ : ∀ {x y} → nat x ≡ nat y → x ≡ y
  nat₁ refl = refl

  word64₁ : ∀ {x y} → word64 x ≡ word64 y → x ≡ y
  word64₁ refl = refl

  float₁ : ∀ {x y} → float x ≡ float y → x ≡ y
  float₁ refl = refl

  char₁ : ∀ {x y} → char x ≡ char y → x ≡ y
  char₁ refl = refl

  string₁ : ∀ {x y} → string x ≡ string y → x ≡ y
  string₁ refl = refl

  name₁ : ∀ {x y} → name x ≡ name y → x ≡ y
  name₁ refl = refl

  lmeta₁ : ∀ {x y} → Literal.meta x ≡ meta y → x ≡ y
  lmeta₁ refl = refl

  clause₁ : ∀ {ps ps′ b b′} → clause ps b ≡ clause ps′ b′ → ps ≡ ps′
  clause₁ refl = refl

  clause₂ : ∀ {ps ps′ b b′} → clause ps b ≡ clause ps′ b′ → b ≡ b′
  clause₂ refl = refl

  absurd-clause₁ : ∀ {ps ps′} → absurd-clause ps ≡ absurd-clause ps′ → ps ≡ ps′
  absurd-clause₁ refl = refl

infix 4 _≟-Visibility_ _≟-Relevance_ _≟-Arg-info_ _≟-Lit_ _≟-AbsTerm_
        _≟-AbsType_ _≟-ArgTerm_ _≟-ArgType_ _≟-ArgPattern_ _≟-Args_
        _≟-Clause_ _≟-Clauses_ _≟-Pattern_ _≟-ArgPatterns_ _≟_
        _≟-Sort_

_≟-Visibility_ : Decidable (_≡_ {A = Visibility})
visible   ≟-Visibility visible   = yes refl
hidden    ≟-Visibility hidden    = yes refl
instance′ ≟-Visibility instance′ = yes refl
visible   ≟-Visibility hidden    = no λ()
visible   ≟-Visibility instance′ = no λ()
hidden    ≟-Visibility visible   = no λ()
hidden    ≟-Visibility instance′ = no λ()
instance′ ≟-Visibility visible   = no λ()
instance′ ≟-Visibility hidden    = no λ()

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
nat x ≟-Lit word64 x₁ = no (λ ())
nat x ≟-Lit float x₁ = no (λ ())
nat x ≟-Lit char x₁ = no (λ ())
nat x ≟-Lit string x₁ = no (λ ())
nat x ≟-Lit name x₁ = no (λ ())
nat x ≟-Lit meta x₁ = no (λ ())
word64 x ≟-Lit word64 x₁ = Dec.map′ (cong word64) word64₁ (x ≟w x₁)
word64 x ≟-Lit nat x₁ = no (λ ())
word64 x ≟-Lit float x₁ = no (λ ())
word64 x ≟-Lit char x₁ = no (λ ())
word64 x ≟-Lit string x₁ = no (λ ())
word64 x ≟-Lit name x₁ = no (λ ())
word64 x ≟-Lit meta x₁ = no (λ ())
float x ≟-Lit nat x₁ = no (λ ())
float x ≟-Lit word64 x₁ = no (λ ())
float x ≟-Lit float x₁ = Dec.map′ (cong float) float₁ (x ≟f x₁)
float x ≟-Lit char x₁ = no (λ ())
float x ≟-Lit string x₁ = no (λ ())
float x ≟-Lit name x₁ = no (λ ())
float x ≟-Lit meta x₁ = no (λ ())
char x ≟-Lit nat x₁ = no (λ ())
char x ≟-Lit word64 x₁ = no (λ ())
char x ≟-Lit float x₁ = no (λ ())
char x ≟-Lit char x₁ = Dec.map′ (cong char) char₁ (x ≟c x₁)
char x ≟-Lit string x₁ = no (λ ())
char x ≟-Lit name x₁ = no (λ ())
char x ≟-Lit meta x₁ = no (λ ())
string x ≟-Lit nat x₁ = no (λ ())
string x ≟-Lit word64 x₁ = no (λ ())
string x ≟-Lit float x₁ = no (λ ())
string x ≟-Lit char x₁ = no (λ ())
string x ≟-Lit string x₁ = Dec.map′ (cong string) string₁ (x ≟s x₁)
string x ≟-Lit name x₁ = no (λ ())
string x ≟-Lit meta x₁ = no (λ ())
name x ≟-Lit nat x₁ = no (λ ())
name x ≟-Lit word64 x₁ = no (λ ())
name x ≟-Lit float x₁ = no (λ ())
name x ≟-Lit char x₁ = no (λ ())
name x ≟-Lit string x₁ = no (λ ())
name x ≟-Lit name x₁ = Dec.map′ (cong name) name₁ (x ≟-Name x₁)
name x ≟-Lit meta x₁ = no (λ ())
meta x ≟-Lit nat x₁ = no (λ ())
meta x ≟-Lit word64 x₁ = no (λ ())
meta x ≟-Lit float x₁ = no (λ ())
meta x ≟-Lit char x₁ = no (λ ())
meta x ≟-Lit string x₁ = no (λ ())
meta x ≟-Lit name x₁ = no (λ ())
meta x ≟-Lit meta x₁ = Dec.map′ (cong meta) lmeta₁ (x ≟-Meta x₁)

mutual
  _≟-AbsTerm_ : Decidable (_≡_ {A = Abs Term})
  abs s a ≟-AbsTerm abs s′ a′ =
    Dec.map′ (cong₂′ abs)
             < abs₁ , abs₂ >
             (s ≟s s′ ×-dec a ≟ a′)

  _≟-AbsType_ : Decidable (_≡_ {A = Abs Type})
  abs s a ≟-AbsType abs s′ a′ =
    Dec.map′ (cong₂′ abs)
             < abs₁ , abs₂ >
             (s ≟s s′ ×-dec a ≟ a′)

  _≟-ArgTerm_ : Decidable (_≡_ {A = Arg Term})
  arg i a ≟-ArgTerm arg i′ a′ =
    Dec.map′ (cong₂′ arg)
             < arg₁ , arg₂ >
             (i ≟-Arg-info i′ ×-dec a ≟ a′)

  _≟-ArgType_ : Decidable (_≡_ {A = Arg Type})
  arg i a ≟-ArgType arg i′ a′ =
    Dec.map′ (cong₂′ arg)
             < arg₁ , arg₂ >
             (i ≟-Arg-info i′ ×-dec a ≟ a′)

  _≟-ArgPattern_ : Decidable (_≡_ {A = Arg Pattern})
  arg i a ≟-ArgPattern arg i′ a′ =
    Dec.map′ (cong₂′ arg)
             < arg₁ , arg₂ >
             (i ≟-Arg-info i′ ×-dec a ≟-Pattern a′)

  _≟-Args_ : Decidable (_≡_ {A = List (Arg Term)})
  []       ≟-Args []       = yes refl
  (x ∷ xs) ≟-Args (y ∷ ys) = Dec.map′ (cong₂′ _∷_) < cons₁ , cons₂ > (x ≟-ArgTerm y ×-dec xs ≟-Args ys)
  []       ≟-Args (_ ∷ _)  = no λ()
  (_ ∷ _)  ≟-Args []       = no λ()

  _≟-Clause_ : Decidable (_≡_ {A = Clause})
  clause ps b ≟-Clause clause ps′ b′ = Dec.map′ (cong₂′ clause) < clause₁ , clause₂ > (ps ≟-ArgPatterns ps′ ×-dec b ≟ b′)
  absurd-clause ps ≟-Clause absurd-clause ps′ = Dec.map′ (cong absurd-clause) absurd-clause₁ (ps ≟-ArgPatterns ps′)
  clause _ _      ≟-Clause absurd-clause _ = no λ()
  absurd-clause _ ≟-Clause clause _ _      = no λ()

  _≟-Clauses_ : Decidable (_≡_ {A = Clauses})
  []       ≟-Clauses []       = yes refl
  (x ∷ xs) ≟-Clauses (y ∷ ys) = Dec.map′ (cong₂′ _∷_) < cons₁ , cons₂ > (x ≟-Clause y ×-dec xs ≟-Clauses ys)
  []       ≟-Clauses (_ ∷ _)  = no λ()
  (_ ∷ _)  ≟-Clauses []       = no λ()

  _≟-Pattern_ : Decidable (_≡_ {A = Pattern})
  con c ps ≟-Pattern con c′ ps′ = Dec.map′ (cong₂′ con) < pcon₁ , pcon₂ > (c ≟-Name c′ ×-dec ps ≟-ArgPatterns ps′)
  con x x₁ ≟-Pattern dot = no (λ ())
  con x x₁ ≟-Pattern var x₂ = no (λ ())
  con x x₁ ≟-Pattern lit x₂ = no (λ ())
  con x x₁ ≟-Pattern proj x₂ = no (λ ())
  con x x₁ ≟-Pattern absurd = no (λ ())
  dot ≟-Pattern con x x₁ = no (λ ())
  dot ≟-Pattern dot = yes refl
  dot ≟-Pattern var x = no (λ ())
  dot ≟-Pattern lit x = no (λ ())
  dot ≟-Pattern proj x = no (λ ())
  dot ≟-Pattern absurd = no (λ ())
  var s ≟-Pattern con x x₁ = no (λ ())
  var s ≟-Pattern dot = no (λ ())
  var s ≟-Pattern var s′ = Dec.map′ (cong var) pvar (s ≟s s′)
  var s ≟-Pattern lit x = no (λ ())
  var s ≟-Pattern proj x = no (λ ())
  var s ≟-Pattern absurd = no (λ ())
  lit x ≟-Pattern con x₁ x₂ = no (λ ())
  lit x ≟-Pattern dot = no (λ ())
  lit x ≟-Pattern var _ = no (λ ())
  lit l ≟-Pattern lit l′ = Dec.map′ (cong lit) plit₁ (l ≟-Lit l′)
  lit x ≟-Pattern proj x₁ = no (λ ())
  lit x ≟-Pattern absurd = no (λ ())
  proj x ≟-Pattern con x₁ x₂ = no (λ ())
  proj x ≟-Pattern dot = no (λ ())
  proj x ≟-Pattern var _ = no (λ ())
  proj x ≟-Pattern lit x₁ = no (λ ())
  proj x ≟-Pattern proj x₁ = Dec.map′ (cong proj) pproj₁ (x ≟-Name x₁)
  proj x ≟-Pattern absurd = no (λ ())
  absurd ≟-Pattern con x x₁ = no (λ ())
  absurd ≟-Pattern dot = no (λ ())
  absurd ≟-Pattern var _ = no (λ ())
  absurd ≟-Pattern lit x = no (λ ())
  absurd ≟-Pattern proj x = no (λ ())
  absurd ≟-Pattern absurd = yes refl

  _≟-ArgPatterns_ : Decidable (_≡_ {A = List (Arg Pattern)})
  []       ≟-ArgPatterns []       = yes refl
  (x ∷ xs) ≟-ArgPatterns (y ∷ ys) = Dec.map′ (cong₂′ _∷_) < cons₁ , cons₂ > (x ≟-ArgPattern y ×-dec xs ≟-ArgPatterns ys)
  []       ≟-ArgPatterns (_ ∷ _)  = no λ()
  (_ ∷ _)  ≟-ArgPatterns []       = no λ()

  _≟_ : Decidable (_≡_ {A = Term})
  var x args ≟ var x′ args′ = Dec.map′ (cong₂′ var) < var₁ , var₂ > (x ≟-ℕ x′          ×-dec args ≟-Args args′)
  con c args ≟ con c′ args′ = Dec.map′ (cong₂′ con) < con₁ , con₂ > (c ≟-Name c′       ×-dec args ≟-Args args′)
  def f args ≟ def f′ args′ = Dec.map′ (cong₂′ def) < def₁ , def₂ > (f ≟-Name f′       ×-dec args ≟-Args args′)
  meta x args ≟ meta x′ args′ = Dec.map′ (cong₂′ meta) < meta₁ , meta₂ > (x ≟-Meta x′   ×-dec args ≟-Args args′)
  lam v t    ≟ lam v′ t′    = Dec.map′ (cong₂′ lam) < lam₁ , lam₂ > (v ≟-Visibility v′ ×-dec t ≟-AbsTerm t′)
  pat-lam cs args ≟ pat-lam cs′ args′ =
                              Dec.map′ (cong₂′ pat-lam) < pat-lam₁ , pat-lam₂ > (cs ≟-Clauses cs′ ×-dec args ≟-Args args′)
  pi t₁ t₂   ≟ pi t₁′ t₂′   = Dec.map′ (cong₂′ pi)  < pi₁  , pi₂  > (t₁ ≟-ArgType t₁′  ×-dec t₂ ≟-AbsType t₂′)
  sort s     ≟ sort s′      = Dec.map′ (cong sort)  sort₁           (s ≟-Sort s′)
  lit l      ≟ lit l′       = Dec.map′ (cong lit)   lit₁           (l ≟-Lit l′)
  unknown    ≟ unknown      = yes refl

  var x args ≟ con c args′ = no λ()
  var x args ≟ def f args′ = no λ()
  var x args ≟ lam v t     = no λ()
  var x args ≟ pi t₁ t₂    = no λ()
  var x args ≟ sort _      = no λ()
  var x args ≟ lit _      = no λ()
  var x args ≟ meta _ _    = no λ()
  var x args ≟ unknown     = no λ()
  con c args ≟ var x args′ = no λ()
  con c args ≟ def f args′ = no λ()
  con c args ≟ lam v t     = no λ()
  con c args ≟ pi t₁ t₂    = no λ()
  con c args ≟ sort _      = no λ()
  con c args ≟ lit _      = no λ()
  con c args ≟ meta _ _    = no λ()
  con c args ≟ unknown     = no λ()
  def f args ≟ var x args′ = no λ()
  def f args ≟ con c args′ = no λ()
  def f args ≟ lam v t     = no λ()
  def f args ≟ pi t₁ t₂    = no λ()
  def f args ≟ sort _      = no λ()
  def f args ≟ lit _      = no λ()
  def f args ≟ meta _ _    = no λ()
  def f args ≟ unknown     = no λ()
  lam v t    ≟ var x args  = no λ()
  lam v t    ≟ con c args  = no λ()
  lam v t    ≟ def f args  = no λ()
  lam v t    ≟ pi t₁ t₂    = no λ()
  lam v t    ≟ sort _      = no λ()
  lam v t    ≟ lit _      = no λ()
  lam v t    ≟ meta _ _    = no λ()
  lam v t    ≟ unknown     = no λ()
  pi t₁ t₂   ≟ var x args  = no λ()
  pi t₁ t₂   ≟ con c args  = no λ()
  pi t₁ t₂   ≟ def f args  = no λ()
  pi t₁ t₂   ≟ lam v t     = no λ()
  pi t₁ t₂   ≟ sort _      = no λ()
  pi t₁ t₂   ≟ lit _      = no λ()
  pi t₁ t₂   ≟ meta _ _    = no λ()
  pi t₁ t₂   ≟ unknown     = no λ()
  sort _     ≟ var x args  = no λ()
  sort _     ≟ con c args  = no λ()
  sort _     ≟ def f args  = no λ()
  sort _     ≟ lam v t     = no λ()
  sort _     ≟ pi t₁ t₂    = no λ()
  sort _     ≟ lit _       = no λ()
  sort _     ≟ meta _ _    = no λ()
  sort _     ≟ unknown     = no λ()
  lit _     ≟ var x args  = no λ()
  lit _     ≟ con c args  = no λ()
  lit _     ≟ def f args  = no λ()
  lit _     ≟ lam v t     = no λ()
  lit _     ≟ pi t₁ t₂    = no λ()
  lit _     ≟ sort _      = no λ()
  lit _     ≟ meta _ _    = no λ()
  lit _     ≟ unknown     = no λ()
  meta _ _   ≟ var x args  = no λ()
  meta _ _   ≟ con c args  = no λ()
  meta _ _   ≟ def f args  = no λ()
  meta _ _   ≟ lam v t     = no λ()
  meta _ _   ≟ pi t₁ t₂    = no λ()
  meta _ _   ≟ sort _      = no λ()
  meta _ _   ≟ lit _       = no λ()
  meta _ _   ≟ unknown     = no λ()
  unknown    ≟ var x args  = no λ()
  unknown    ≟ con c args  = no λ()
  unknown    ≟ def f args  = no λ()
  unknown    ≟ lam v t     = no λ()
  unknown    ≟ pi t₁ t₂    = no λ()
  unknown    ≟ sort _      = no λ()
  unknown    ≟ lit _       = no λ()
  unknown    ≟ meta _ _    = no λ()
  pat-lam _ _ ≟ var x args  = no λ()
  pat-lam _ _ ≟ con c args  = no λ()
  pat-lam _ _ ≟ def f args  = no λ()
  pat-lam _ _ ≟ lam v t     = no λ()
  pat-lam _ _ ≟ pi t₁ t₂    = no λ()
  pat-lam _ _ ≟ sort _      = no λ()
  pat-lam _ _ ≟ lit _       = no λ()
  pat-lam _ _ ≟ meta _ _    = no λ()
  pat-lam _ _ ≟ unknown     = no λ()
  var x args  ≟ pat-lam _ _ = no λ()
  con c args  ≟ pat-lam _ _ = no λ()
  def f args  ≟ pat-lam _ _ = no λ()
  lam v t     ≟ pat-lam _ _ = no λ()
  pi t₁ t₂    ≟ pat-lam _ _ = no λ()
  sort _      ≟ pat-lam _ _ = no λ()
  lit _       ≟ pat-lam _ _ = no λ()
  meta _ _    ≟ pat-lam _ _ = no λ()
  unknown     ≟ pat-lam _ _ = no λ()

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
