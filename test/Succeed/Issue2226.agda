-- Andreas, 2018-03-12
-- The fix for #2963 introduced a change in the quotation behavior
-- of method definitions inside a record.

open import Agda.Builtin.Float
open import Agda.Builtin.Reflection
open import Agda.Builtin.List
open import Agda.Builtin.Unit
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma

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

pattern rArg v q x = arg (arg-info v (modality relevant q)) x
pattern vArg x = rArg visible quantity-ω x
pattern hArg x = rArg hidden  quantity-ω x
pattern iArg x = rArg instance′ quantity-ω x
pattern `? q = rArg hidden q unknown

pattern fun₀ b = function (clause [] [] b ∷ [])
pattern fun₁ tel p b = function (clause tel (p ∷ []) b ∷ [])
pattern fun₂ tel p q b = function (clause tel (p ∷ q ∷ []) b ∷ [])

-- foo {{r}} = Foo.foo {_} r
foo-def :
  getDef foo ≡
  fun₂
    (("A" , hArg (agda-sort (lit 0))) ∷
     ("r" , iArg (def (quote Foo) (vArg (var 0 []) ∷ []))) ∷ [])
    (hArg (var 1)) (iArg (var 0))
    (def (quote Foo.foo) (`? quantity-0 ∷ vArg (var 0 []) ∷ []))
foo-def = refl

-- Andreas, 2018-03-12: Behavior before fix of #2963:
-- foo₁ {{r}} = Foo.foo₁ {_} r
-- foo₁-def : getDef foo₁ ≡ fun₁ (iArg (var "r")) (def (quote Foo.foo₁) (`? ∷ vArg (var 0 []) ∷ []))
-- NOW:
-- foo₁ {A} {{r}} = Foo.foo₁ {A} r
foo₁-def : getDef foo₁ ≡ fun₂
             (("A" , hArg (agda-sort (lit 0))) ∷ ("r" , iArg (def (quote Foo) (vArg (var 0 []) ∷ []))) ∷ [])
             (hArg (var 1)) (iArg (var 0))
             (def (quote Foo.foo₁) (hArg (var 1 []) ∷ vArg (var 0 []) ∷ []))
foo₁-def = refl

-- bar = foo {_} FooA
bar-def :
  getDef bar ≡
  fun₀ (def (quote Foo.foo)
            (`? quantity-0 ∷ vArg (def (quote FooA) []) ∷ []))
bar-def = refl

-- bar₁ = Foo.foo₁ {A} FooA
bar₁-def : getDef bar₁ ≡ fun₀ (def (quote Foo.foo₁) (hArg (def (quote A) [])  ∷ vArg (def (quote FooA) []) ∷ []))
bar₁-def =  refl

-- bar₂ = foo₂ {_} {FooA}
bar₂-def :
  getDef bar₂ ≡
  fun₀ (def (quote foo₂)
            (`? quantity-ω ∷ hArg (def (quote FooA) []) ∷ []))
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
