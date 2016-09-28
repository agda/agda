
open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit
open import Agda.Builtin.List
open import Agda.Builtin.Equality

infixl 4 _>>=_
_>>=_ = bindTC

data Tm : Set where
  [_] : Term → Tm

macro
  qType : Term → Term → TC ⊤
  qType t hole = inferType t >>= quoteTC >>= unify hole

  qTerm : Term → Term → TC ⊤
  qTerm t hole = quoteTC t >>= unify hole

  unQ : Tm → Term → TC ⊤
  unQ [ t ] hole = unify hole t

postulate
  X : Set
  x y z : X

id : (A : Set) → A → A
id _ x = x

record R (A B : Set) : Set₁ where
  field
    F : X → X → X → Set

  bar : F x y z → Term
  bar fx = qType fx  -- result: F z   (x y are dropped)

  check-bar : F x y z → F x y z
  check-bar fx = id (unQ [ bar fx ]) fx

baz : ∀ {A B} (r : R A B) → R.F r x y z → Term
baz r fx = qType fx

check-baz : ∀ {A B} (r : R A B) → R.F r x y z → R.F r x y z
check-baz r fx = id (unQ [ baz r fx ]) fx

module M (A B : Set) where

  data D : Set where
    d : D

  `d = qTerm d
  d′ = unquote (unify `d)

`Md = qTerm (M.d {X} {X})

Md : M.D X X
Md = unquote (unify `Md)
