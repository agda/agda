------------------------------------------------------------------------
-- Support for reflection
------------------------------------------------------------------------

module Reflection where

open import Data.Bool as Bool using (Bool); open Bool.Bool
open import Data.List using (List); open Data.List.List
open import Data.Nat using (ℕ) renaming (_≟_ to _≟-ℕ_)
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.TrustMe
open import Relation.Nullary
open import Relation.Nullary.Decidable as Dec

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

-- Is the argument implicit? (Here true stands for implicit and false
-- for explicit.)

data Implicit? : Set where
  implicit explicit : Implicit?

{-# BUILTIN HIDING  Implicit?  #-}
{-# BUILTIN HIDDEN  implicit   #-}
{-# BUILTIN VISIBLE explicit   #-}

data Relevant? : Set where
  relevant irrelevant forced : Relevant?

{-# BUILTIN RELEVANCE  Relevant?  #-}
{-# BUILTIN RELEVANT   relevant   #-}
{-# BUILTIN IRRELEVANT irrelevant #-}
{-# BUILTIN FORCED     forced     #-}

-- Arguments.

data Arg A : Set where
  arg : (im? : Implicit?) (r? : Relevant?) (x : A) → Arg A

{-# BUILTIN ARG    Arg #-}
{-# BUILTIN ARGARG arg #-}

-- Terms.

mutual
  data Term : Set where
    -- Variable applied to arguments.
    var     : (x : ℕ) (args : List (Arg Term)) → Term
    -- Constructor applied to arguments.
    con     : (c : Name) (args : List (Arg Term)) → Term
    -- Identifier applied to arguments.
    def     : (f : Name) (args : List (Arg Term)) → Term
    -- Explicit or implicit λ abstraction.
    lam     : (im? : Implicit?) (t : Term) → Term
    -- Pi-type.
    pi      : (t₁ : Arg Type) (t₂ : Type) → Term
    -- An arbitrary sort (Set, for instance).
    sort    : Sort → Term
    -- Anything else.
    unknown : Term

  data Type : Set where
    el : (s : Sort) (t : Term) → Type

  data Sort : Set where
    set     : (t : Term) → Sort
    lit     : (n : ℕ) → Sort
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
{-# BUILTIN AGDATERMUNSUPPORTED unknown #-}
{-# BUILTIN AGDATYPEEL          el      #-}
{-# BUILTIN AGDASORTSET         set     #-}
{-# BUILTIN AGDASORTLIT         lit     #-}
{-# BUILTIN AGDASORTUNSUPPORTED unknown #-}

------------------------------------------------------------------------
-- Term equality is decidable

-- Boring helper functions.

private

  arg₁ : ∀ {A im? im?′ r? r?′} {x x′ : A} →
         arg im? r? x ≡ arg im?′ r?′ x′ → im? ≡ im?′
  arg₁ refl = refl

  arg₂ : ∀ {A im? im?′ r? r?′} {x x′ : A} →
         arg im? r? x ≡ arg im?′ r?′ x′ → r? ≡ r?′
  arg₂ refl = refl

  arg₃ : ∀ {A im? im?′ r? r?′} {x x′ : A} →
         arg im? r? x ≡ arg im?′ r?′ x′ → x ≡ x′
  arg₃ refl = refl

  cons₁ : ∀ {A : Set} {x y} {xs ys : List A} → x ∷ xs ≡ y ∷ ys → x ≡ y
  cons₁ refl = refl

  cons₂ : ∀ {A : Set} {x y} {xs ys : List A} → x ∷ xs ≡ y ∷ ys → xs ≡ ys
  cons₂ refl = refl

  var₁ : ∀ {x x′ args args′} → var x args ≡ var x′ args′ → x ≡ x′
  var₁ refl = refl

  var₂ : ∀ {x x′ args args′} → var x args ≡ var x′ args′ → args ≡ args′
  var₂ refl = refl

  con₁ : ∀ {c c′ args args′} → con c args ≡ con c′ args′ → c ≡ c′
  con₁ refl = refl

  con₂ : ∀ {c c′ args args′} → con c args ≡ con c′ args′ → args ≡ args′
  con₂ refl = refl

  def₁ : ∀ {f f′ args args′} → def f args ≡ def f′ args′ → f ≡ f′
  def₁ refl = refl

  def₂ : ∀ {f f′ args args′} → def f args ≡ def f′ args′ → args ≡ args′
  def₂ refl = refl

  lam₁ : ∀ {im? im?′ t t′} → lam im? t ≡ lam im?′ t′ → im? ≡ im?′
  lam₁ refl = refl

  lam₂ : ∀ {im? im?′ t t′} → lam im? t ≡ lam im?′ t′ → t ≡ t′
  lam₂ refl = refl

  pi₁ : ∀ {t₁ t₁′ t₂ t₂′} → pi t₁ t₂ ≡ pi t₁′ t₂′ → t₁ ≡ t₁′
  pi₁ refl = refl

  pi₂ : ∀ {t₁ t₁′ t₂ t₂′} → pi t₁ t₂ ≡ pi t₁′ t₂′ → t₂ ≡ t₂′
  pi₂ refl = refl

  sort₁ : ∀ {x y} → sort x ≡ sort y → x ≡ y
  sort₁ refl = refl

  set₁ : ∀ {x y} → set x ≡ set y → x ≡ y
  set₁ refl = refl

  lit₁ : ∀ {x y} → lit x ≡ lit y → x ≡ y
  lit₁ refl = refl

  el₁ : ∀ {s s′ t t′} → el s t ≡ el s′ t′ → s ≡ s′
  el₁ refl = refl

  el₂ : ∀ {s s′ t t′} → el s t ≡ el s′ t′ → t ≡ t′
  el₂ refl = refl

_≟-Implicit?_ : Decidable (_≡_ {A = Implicit?})
implicit ≟-Implicit? implicit = yes refl
explicit ≟-Implicit? explicit = yes refl
implicit ≟-Implicit? explicit = no λ()
explicit ≟-Implicit? implicit = no λ()

_≟-Relevant?_ : Decidable (_≡_ {A = Relevant?})
relevant   ≟-Relevant? relevant   = yes refl
irrelevant ≟-Relevant? irrelevant = yes refl
forced     ≟-Relevant? forced     = yes refl
relevant   ≟-Relevant? irrelevant = no λ()
relevant   ≟-Relevant? forced     = no λ()
irrelevant ≟-Relevant? relevant   = no λ()
irrelevant ≟-Relevant? forced     = no λ()
forced     ≟-Relevant? relevant   = no λ()
forced     ≟-Relevant? irrelevant = no λ()

mutual
  infix 4 _≟_ _≟-Args_ _≟-ArgType_

  -- We have to specialise the Arg and List equality decisions to please the termination checker...

  _≟-ArgTerm_ : Decidable (_≡_ {A = Arg Term})
  arg e r a ≟-ArgTerm arg e′ r′ a′
    = Dec.map₃′ (cong₃ arg) arg₁ arg₂ arg₃ (e ≟-Implicit? e′) (r ≟-Relevant? r′) (a ≟ a′)

  _≟-ArgType_ : Decidable (_≡_ {A = Arg Type})
  arg e r a ≟-ArgType arg e′ r′ a′
    = Dec.map₃′ (cong₃ arg) arg₁ arg₂ arg₃ (e ≟-Implicit? e′) (r ≟-Relevant? r′) (a ≟-Type a′)

  _≟-Args_ : Decidable (_≡_ {A = List (Arg Term)})
  []       ≟-Args []         = yes refl
  (x ∷ xs) ≟-Args (y ∷ ys)  = Dec.map₂′ (cong₂ _∷_) cons₁ cons₂ (x ≟-ArgTerm y) (xs ≟-Args ys)
  []       ≟-Args (_ ∷ _)    = no λ()
  (_ ∷ _)  ≟-Args []         = no λ()

  _≟_ : Decidable (_≡_ {A = Term})
  var x args ≟ var x′ args′ = Dec.map₂′ (cong₂ var) var₁ var₂ (x ≟-ℕ x′) (args ≟-Args args′)
  con c args ≟ con c′ args′ = Dec.map₂′ (cong₂ con) con₁ con₂ (c ≟-Name c′) (args ≟-Args args′)
  def f args ≟ def f′ args′ = Dec.map₂′ (cong₂ def) def₁ def₂ (f ≟-Name f′) (args ≟-Args args′)
  lam im? t  ≟ lam im?′ t′  = Dec.map₂′ (cong₂ lam) lam₁ lam₂ (im? ≟-Implicit? im?′) (t ≟ t′)
  pi t₁ t₂   ≟ pi t₁′ t₂′  = Dec.map₂′ (cong₂ pi)  pi₁  pi₂  (t₁ ≟-ArgType t₁′) (t₂ ≟-Type t₂′)
  sort s     ≟ sort s′      = Dec.map′ (cong sort) sort₁ (s ≟-Sort s′)
  unknown    ≟ unknown      = yes refl

  var x args ≟ con c args′  = no λ()
  var x args ≟ def f args′  = no λ()
  var x args ≟ lam im? t    = no λ()
  var x args ≟ pi t₁ t₂     = no λ()
  var x args ≟ sort _       = no λ()
  var x args ≟ unknown      = no λ()
  con c args ≟ var x args′  = no λ()
  con c args ≟ def f args′  = no λ()
  con c args ≟ lam im? t    = no λ()
  con c args ≟ pi t₁ t₂     = no λ()
  con c args ≟ sort _       = no λ()
  con c args ≟ unknown      = no λ()
  def f args ≟ var x args′  = no λ()
  def f args ≟ con c args′  = no λ()
  def f args ≟ lam im? t    = no λ()
  def f args ≟ pi t₁ t₂     = no λ()
  def f args ≟ sort _       = no λ()
  def f args ≟ unknown      = no λ()
  lam im? t  ≟ var x args   = no λ()
  lam im? t  ≟ con c args   = no λ()
  lam im? t  ≟ def f args   = no λ()
  lam im? t  ≟ pi t₁ t₂     = no λ()
  lam im? t  ≟ sort _       = no λ()
  lam im? t  ≟ unknown      = no λ()
  pi t₁ t₂   ≟ var x args   = no λ()
  pi t₁ t₂   ≟ con c args   = no λ()
  pi t₁ t₂   ≟ def f args   = no λ()
  pi t₁ t₂   ≟ lam im? t    = no λ()
  pi t₁ t₂   ≟ sort _       = no λ()
  pi t₁ t₂   ≟ unknown      = no λ()
  sort _     ≟ var x args   = no λ()
  sort _     ≟ con c args   = no λ()
  sort _     ≟ def f args   = no λ()
  sort _     ≟ lam im? t    = no λ()
  sort _     ≟ pi t₁ t₂     = no λ()
  sort _     ≟ unknown      = no λ()
  unknown    ≟ var x args   = no λ()
  unknown    ≟ con c args   = no λ()
  unknown    ≟ def f args   = no λ()
  unknown    ≟ lam im? t    = no λ()
  unknown    ≟ pi t₁ t₂     = no λ()
  unknown    ≟ sort _       = no λ()

  _≟-Type_ : Decidable (_≡_ {A = Type})
  el s t ≟-Type el s′ t′ = Dec.map₂′ (cong₂ el) el₁ el₂ (s ≟-Sort s′) (t ≟ t′)

  _≟-Sort_ : Decidable (_≡_ {A = Sort})
  set t   ≟-Sort set t′  = Dec.map′ (cong set) set₁ (t ≟ t′)
  lit n   ≟-Sort lit n′  = Dec.map′ (cong lit) lit₁ (n ≟-ℕ n′)
  unknown ≟-Sort unknown = yes refl
  set _   ≟-Sort lit _   = no λ()
  set _   ≟-Sort unknown = no λ()
  lit _   ≟-Sort set _   = no λ()
  lit _   ≟-Sort unknown = no λ()
  unknown ≟-Sort set _   = no λ()
  unknown ≟-Sort lit _   = no λ()
