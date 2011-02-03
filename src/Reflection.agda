------------------------------------------------------------------------
-- Support for reflection
------------------------------------------------------------------------

module Reflection where

open import Data.Bool as Bool using (Bool); open Bool.Bool
open import Data.List using (List); open Data.List.List
open import Data.Nat as Nat using (ℕ)
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.TrustMe
open import Relation.Nullary

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

Implicit? = Bool

-- Arguments.

data Arg A : Set where
  arg : (im? : Implicit?) (x : A) → Arg A

{-# BUILTIN ARG    Arg #-}
{-# BUILTIN ARGARG arg #-}

-- Terms.

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
  pi      : (t₁ : Arg Term) (t₂ : Term) → Term
  -- An arbitrary sort (Set, for instance).
  sort    : Term
  -- Anything.
  unknown : Term

{-# BUILTIN AGDATERM            Term    #-}
{-# BUILTIN AGDATERMVAR         var     #-}
{-# BUILTIN AGDATERMCON         con     #-}
{-# BUILTIN AGDATERMDEF         def     #-}
{-# BUILTIN AGDATERMLAM         lam     #-}
{-# BUILTIN AGDATERMPI          pi      #-}
{-# BUILTIN AGDATERMSORT        sort    #-}
{-# BUILTIN AGDATERMUNSUPPORTED unknown #-}

------------------------------------------------------------------------
-- Term equality is decidable

-- Boring helper functions.

private

  arg₁ : ∀ {A im? im?′} {x x′ : A} →
         arg im? x ≡ arg im?′ x′ → im? ≡ im?′
  arg₁ refl = refl

  arg₂ : ∀ {A im? im?′} {x x′ : A} →
         arg im? x ≡ arg im?′ x′ → x ≡ x′
  arg₂ refl = refl

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

mutual

  infix 4 _≟-Arg_ _≟-Args_ _≟_

  _≟-Arg_ : Decidable (_≡_ {A = Arg Term})
  arg e a ≟-Arg arg e′ a′ with Bool._≟_ e e′ | a ≟ a′
  arg e a ≟-Arg arg .e .a | yes refl | yes refl = yes refl
  arg e a ≟-Arg arg e′ a′ | no  e≢e′ | _        = no (e≢e′ ∘ arg₁)
  arg e a ≟-Arg arg e′ a′ | _        | no a≢a′  = no (a≢a′ ∘ arg₂)

  _≟-Args_ : Decidable (_≡_ {A = List (Arg Term)})
  []         ≟-Args []           = yes refl
  (a ∷ args) ≟-Args (a′ ∷ args′) with a ≟-Arg a′ | args ≟-Args args′
  (a ∷ args) ≟-Args (.a ∷ .args) | yes refl | yes refl      = yes refl
  (a ∷ args) ≟-Args (a′ ∷ args′) | no a≢a′  | _             = no (a≢a′ ∘ cons₁)
  (a ∷ args) ≟-Args (a′ ∷ args′) | _        | no args≢args′ = no (args≢args′ ∘ cons₂)
  []         ≟-Args (_ ∷ _)      = no λ()
  (_ ∷ _)    ≟-Args []           = no λ()

  _≟_ : Decidable (_≡_ {A = Term})
  var x args ≟ var x′ args′ with Nat._≟_ x x′ | args ≟-Args args′
  var x args ≟ var .x .args | yes refl | yes refl      = yes refl
  var x args ≟ var x′ args′ | no x≢x′  | _             = no (x≢x′ ∘ var₁)
  var x args ≟ var x′ args′ | _        | no args≢args′ = no (args≢args′ ∘ var₂)
  con c args ≟ con c′ args′ with c ≟-Name c′ | args ≟-Args args′
  con c args ≟ con .c .args | yes refl | yes refl      = yes refl
  con c args ≟ con c′ args′ | no c≢c′  | _             = no (c≢c′ ∘ con₁)
  con c args ≟ con c′ args′ | _        | no args≢args′ = no (args≢args′ ∘ con₂)
  def f args ≟ def f′ args′ with f ≟-Name f′ | args ≟-Args args′
  def f args ≟ def .f .args | yes refl | yes refl      = yes refl
  def f args ≟ def f′ args′ | no f≢f′  | _             = no (f≢f′ ∘ def₁)
  def f args ≟ def f′ args′ | _        | no args≢args′ = no (args≢args′ ∘ def₂)
  lam im? t  ≟ lam im?′ t′  with Bool._≟_ im? im?′ | t ≟ t′
  lam im? t  ≟ lam .im? .t  | yes refl    | yes refl = yes refl
  lam im? t  ≟ lam im?′ t′  | no im?≢im?′ | _        = no (im?≢im?′ ∘ lam₁)
  lam im? t  ≟ lam im?′ t′  | _           | no t≢t′  = no (t≢t′ ∘ lam₂)
  pi t₁ t₂   ≟ pi t₁′ t₂′   with t₁ ≟-Arg t₁′ | t₂ ≟ t₂′
  pi t₁ t₂   ≟ pi .t₁ .t₂   | yes refl  | yes refl  = yes refl
  pi t₁ t₂   ≟ pi t₁′ t₂′   | no t₁≢t₁′ | _         = no (t₁≢t₁′ ∘ pi₁)
  pi t₁ t₂   ≟ pi t₁′ t₂′   | _         | no t₂≢t₂′ = no (t₂≢t₂′ ∘ pi₂)
  sort       ≟ sort         = yes refl
  unknown    ≟ unknown      = yes refl

  var x args ≟ con c args′  = no λ()
  var x args ≟ def f args′  = no λ()
  var x args ≟ lam im? t    = no λ()
  var x args ≟ pi t₁ t₂     = no λ()
  var x args ≟ sort         = no λ()
  var x args ≟ unknown      = no λ()
  con c args ≟ var x args′  = no λ()
  con c args ≟ def f args′  = no λ()
  con c args ≟ lam im? t    = no λ()
  con c args ≟ pi t₁ t₂     = no λ()
  con c args ≟ sort         = no λ()
  con c args ≟ unknown      = no λ()
  def f args ≟ var x args′  = no λ()
  def f args ≟ con c args′  = no λ()
  def f args ≟ lam im? t    = no λ()
  def f args ≟ pi t₁ t₂     = no λ()
  def f args ≟ sort         = no λ()
  def f args ≟ unknown      = no λ()
  lam im? t  ≟ var x args   = no λ()
  lam im? t  ≟ con c args   = no λ()
  lam im? t  ≟ def f args   = no λ()
  lam im? t  ≟ pi t₁ t₂     = no λ()
  lam im? t  ≟ sort         = no λ()
  lam im? t  ≟ unknown      = no λ()
  pi t₁ t₂   ≟ var x args   = no λ()
  pi t₁ t₂   ≟ con c args   = no λ()
  pi t₁ t₂   ≟ def f args   = no λ()
  pi t₁ t₂   ≟ lam im? t    = no λ()
  pi t₁ t₂   ≟ sort         = no λ()
  pi t₁ t₂   ≟ unknown      = no λ()
  sort       ≟ var x args   = no λ()
  sort       ≟ con c args   = no λ()
  sort       ≟ def f args   = no λ()
  sort       ≟ lam im? t    = no λ()
  sort       ≟ pi t₁ t₂     = no λ()
  sort       ≟ unknown      = no λ()
  unknown    ≟ var x args   = no λ()
  unknown    ≟ con c args   = no λ()
  unknown    ≟ def f args   = no λ()
  unknown    ≟ lam im? t    = no λ()
  unknown    ≟ pi t₁ t₂     = no λ()
  unknown    ≟ sort         = no λ()
