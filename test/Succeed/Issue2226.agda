
open import Agda.Builtin.Float
open import Agda.Builtin.Reflection
open import Agda.Builtin.List
open import Agda.Builtin.Unit
open import Agda.Builtin.Equality

infixl 6 _>>=_
_>>=_ = bindTC

macro
  getDef : Name → Term → TC ⊤
  getDef x a = getDefinition x >>= quoteTC >>= unify a

record Foo (A : Set) : Set where
  constructor mkFoo
  field foo : A
  foo₁ : A
  foo₁ = foo

open module FooI = Foo {{...}}

postulate
  A : Set
  instance FooA : Foo A

-- Projection-like
foo₂ : {A : Set} {r : Foo A} → A
foo₂ {r = mkFoo x} = x

bar : A
bar = foo

bar₁ : A
bar₁ = foo₁

bar₂ : A
bar₂ = foo₂ {r = FooA}

pattern rArg v x = arg (arg-info v relevant) x
pattern vArg x = rArg visible x
pattern hArg x = rArg hidden  x
pattern iArg x = rArg instance′ x
pattern `? = hArg unknown

pattern fun₀ b = function (clause [] b ∷ [])
pattern fun₁ p b = function (clause (p ∷ []) b ∷ [])

-- foo {{r}} = Foo.foo {_} r
foo-def : getDef foo ≡ fun₁ (iArg (var "r")) (def (quote Foo.foo) (`? ∷ vArg (var 0 []) ∷ []))
foo-def = refl

-- foo₁ {{r}} = Foo.foo₁ {_} r
foo₁-def : getDef foo₁ ≡ fun₁ (iArg (var "r")) (def (quote Foo.foo₁) (`? ∷ vArg (var 0 []) ∷ []))
foo₁-def = refl

-- bar = foo {_} FooA
bar-def : getDef bar ≡ fun₀ (def (quote Foo.foo) (`? ∷ vArg (def (quote FooA) []) ∷ []))
bar-def = refl

-- bar₁ = foo₁ {_} {{FooA}}
bar₁-def : getDef bar₁ ≡ fun₀ (def (quote Foo.foo₁) (`? ∷ vArg (def (quote FooA) []) ∷ []))
bar₁-def =  refl

-- bar₂ = foo₂ {_} {FooA}
bar₂-def : getDef bar₂ ≡ fun₀ (def (quote foo₂) (`? ∷ hArg (def (quote FooA) []) ∷ []))
bar₂-def =  refl

--- Originally reported test case ---

defToTerm : Name → Definition → List (Arg Term) → Term
defToTerm _ (function cs) as = pat-lam cs as
defToTerm _ (data-cons d) as = con d as
defToTerm _ _ _ = unknown

derefImmediate : Term → TC Term
derefImmediate (def f args) = getDefinition f >>= λ f' → returnTC (defToTerm f f' args)
derefImmediate x = returnTC x

reflectTerm : Name → TC Term
reflectTerm n = getType n >>= λ ty → getDefinition n >>= λ x →
                derefImmediate (defToTerm n x []) >>= λ x → checkType x ty

macro
  reflect : Name → Term → TC ⊤
  reflect n a = reflectTerm n >>= quoteTC >>= unify a

{- Define typeclass Semigroup a => Plus a -}

record SemigroupLaws {ℓ} (t : Set ℓ) : Set ℓ where
  infixr 5 _++_
  field
    _++_ : t → t → t
    -- associative : ∀ {a b c} → (a ++ b) ++ c ≡ a ++ b ++ c

record PlusOp {ℓ} (t : Set ℓ) : Set ℓ where
  field
    semigroup : SemigroupLaws t

  infixr 6 _+_
  _+_ = SemigroupLaws._++_ semigroup

instance
  floatPlus : PlusOp Float
  floatPlus = record { semigroup = record { _++_ = Agda.Builtin.Float.primFloatPlus } }

open PlusOp {{...}}

-- The issue:

works : Float
works = PlusOp._+_ floatPlus 3.0 5.0

resultWorks : Term
resultWorks = reflect works

fails : Float
fails = 3.0 + 5.0

resultFails : Term
resultFails = reflect fails
