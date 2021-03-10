-- Andreas, 2020-02-06, issue #906, and #942 #2068 #3136 #3431 #4391 #4418
--
-- Termination checker now tries to reduce calls away
-- using non-recursive clauses.
--
-- This fixes the problem that for dependent copattern definitions
-- the earlier, non-recursive clauses get into non-guarded positions
-- in later clauses via Agda's constraint solver, and there confuse
-- the termination checker.

module Issue906EtAl where

module Issue906 where

  {- Globular types as a coinductive record -}
  record Glob : Set1 where
    coinductive
    field
      Ob : Set
      Hom : (a b : Ob) → Glob
  open Glob

  record Unit : Set where

  data _==_ {A : Set} (a : A) : A → Set where
    refl : a == a

  {- The terminal globular type -}
  Unit-glob : Glob
  Ob Unit-glob = Unit
  Hom Unit-glob _ _ = Unit-glob

  {- The tower of identity types -}
  Id-glob : (A : Set) → Glob
  Ob (Id-glob A) = A
  Hom (Id-glob A) a b = Id-glob (a == b)


module Issue907 where

  data _==_ {A : Set} (a : A) : A → Set where
    idp : a == a

  -- Coinductive equivalences
  record CoEq (A B : Set) : Set where
    coinductive
    constructor coEq
    field to : A → B
          from : B → A
          eq : (a : A) (b : B) → CoEq (a == from b) (to a == b)

  open CoEq public

  id-CoEq : (A : Set) → CoEq A A
  to   (id-CoEq A) a   = a
  from (id-CoEq A) b   = b
  eq   (id-CoEq A) a b = id-CoEq _ -- Keep underscore!
    -- Solution: (a == from (id-CoEq A) b)
    -- contains recursive call

module Issue942 where

  record Sigma (A : Set)(P : A → Set) : Set where
    constructor _,_
    field
      fst : A
      snd : P fst
  open Sigma

  postulate
    A : Set
    x : A
    P Q : A → Set
    Px : P x
    f  : ∀ {x} → P x → Q x

  ex : Sigma A Q
  ex = record
         { fst = x
         ; snd = f Px -- goal: P x
         }

  ex' : Sigma A Q
  ex' = x , f Px -- goal: P x

  ex'' : Sigma A Q
  fst ex'' = x
  snd ex'' = f Px -- goal: P (fst ex'')

module Issue2068-OP where

  data _==_ {A : Set} : A → A → Set where
    refl : {a : A} → a == a

  data Bool : Set where
    tt : Bool
    ff : Bool

  record TwoEqualFunctions : Set₁ where
    field
      A : Set
      B : Set
      f : A → B
      g : A → B
      p : f == g

  postulate
    funext : {A B : Set} {f g : A → B} → ((a : A) → f a == g a) → f == g

  identities : TwoEqualFunctions
  TwoEqualFunctions.A identities = Bool
  TwoEqualFunctions.B identities = Bool
  TwoEqualFunctions.f identities x = x
  TwoEqualFunctions.g identities = λ{tt → tt ; ff → ff}
  TwoEqualFunctions.p identities = funext (λ{tt → refl ; ff → refl})

module Issue2068b where

  data _==_ {A : Set} : (a : A) → A → Set where
    refl : (a : A) → a == a

  data Unit : Set where
    unit : Unit

  record R : Set₁ where
    field
      f : Unit → Unit
      p : f == λ x → x

  postulate
    extId : (f : Unit → Unit) → (∀ a → f a == a) → f == λ x → x

  test : R
  R.f test = λ{ unit → unit }
  R.p test = extId _ λ{ unit → refl _ }
  -- R.p test = extId {! R.f test !} λ{unit → refl {! R.f test unit !}}

module Issue2068c where

  record _×_ (A B : Set) : Set where
    field fst : A
          snd : B
  open _×_

  test : ∀{A} (a : A) → (A → A) × (A → A)
  fst (test a) x = a
  snd (test a) x = fst (test a) (snd (test a) x)

module Issue3136 (A : Set) where

  -- Andreas, 2018-07-22, issue #3136
  -- WAS: Internal error when printing termination errors

  postulate
    any : {X : Set} → X
    x : A
    P : A → Set

  record C : Set where
    field
      a : A
      b : P a

  c : C
  c = λ where
    .C.a → x
    .C.b → λ where
      → any

  -- NOW: succeeds

module Issue3413 where

  open import Agda.Builtin.Sigma
  open import Agda.Builtin.Equality

  postulate
    A : Set
    P : ∀{X : Set} → X → Set

  record Bob : Set₁ where
    field
      RE : Set
      resp : RE → Set

  open Bob

  bob : Bob
  bob .RE     = A
  bob .resp e = Σ (P e) λ {x → A}

module Issue4391 where

  record GlobSet : Set₁ where
    coinductive
    field
      cells : Set
      morphisms : cells → cells → GlobSet

  open GlobSet public

  record GlobSetMorphism (G H : GlobSet) : Set where
    coinductive
    field
      func : cells G → cells H
      funcMorphisms : (x y : cells G)
                    → GlobSetMorphism (morphisms G x y)
                                      (morphisms H (func x) (func y))

  open GlobSetMorphism public

  gComp : {G H I : GlobSet} → GlobSetMorphism H I → GlobSetMorphism G H → GlobSetMorphism G I
  func (gComp ϕ ψ) x = func ϕ (func ψ x)
  funcMorphisms (gComp ϕ ψ) x y = gComp (funcMorphisms ϕ (func ψ x) (func ψ y)) (funcMorphisms ψ x y)

module Issue4391Nisse where

  record GlobSet : Set₁ where
    coinductive
    field
      cells     : Set
      morphisms : cells → cells → GlobSet

  open GlobSet public

  mutual

    record GlobSetMorphism (G H : GlobSet) : Set where
      inductive
      field
        func          : cells G → cells H
        funcMorphisms : (x y : cells G) →
                        GlobSetMorphism′
                          (morphisms G x y)
                          (morphisms H (func x) (func y))

    record GlobSetMorphism′ (G H : GlobSet) : Set where
      coinductive
      field
        force : GlobSetMorphism G H

  open GlobSetMorphism  public
  open GlobSetMorphism′ public

  works fails :
    {G H I : GlobSet} →
    GlobSetMorphism H I → GlobSetMorphism G H → GlobSetMorphism G I

  works ϕ ψ = record
    { func          = λ x → func ϕ (func ψ x)
    ; funcMorphisms = λ { x y .force →
        works (funcMorphisms ϕ (func ψ x) (func ψ y) .force)
              (funcMorphisms ψ x y .force) }
    }

  fails ϕ ψ .func          = λ x → func ϕ (func ψ x)
  fails ϕ ψ .funcMorphisms = λ { x y .force →
    fails (funcMorphisms ϕ (func ψ x) (func ψ y) .force)
          (funcMorphisms ψ x y .force) }


module Issue4418 {l}
  (Index : Set l)
  (Shape : Index → Set l)
  (Position : (i : Index) → Shape i → Set l)
  (index : (i : Index) → (s : Shape i) → Position i s → Index) where

  record M (i : Index) : Set l where
    coinductive
    field shape : Shape i
    field children : (p : Position i shape) → M (index i shape p)

  open M

  record MBase (Rec : Index → Set l) (i : Index) : Set l where
    coinductive
    field shapeB : Shape i
    field childrenB : (p : Position i shapeB) → Rec (index i shapeB p)

  open MBase

  module _ (S : Index → Set l) (u : ∀ {i} → S i → MBase S i) where

    unroll : ∀ i → S i → M i
    unroll i s .shape      = u s .shapeB
    unroll i s .children p = unroll _ (u s .childrenB p)
      -- Underscore solved as:  index i (u s .shapeB) p
