
open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Reflection
open import Agda.Builtin.Equality

variable
  A B : Set

data Eqn (A : Set) : Set where
  eqn : (x y : A) → x ≡ y → Eqn A

infix 3 _==_
pattern _==_ x y = eqn x y refl

infixl 0 such-that
syntax such-that a (λ x → P) p = a is x such-that p proves P
such-that : (x : A) (P : A → Set) → P x → A
such-that x _ _ = x

infix -1 check_
check_ : A → ⊤
check _ = _

infixl -2 _and_
_and_ : ⊤ → A → ⊤
_ and _ = _

-- Record fields can be marked with @tactic

data ShouldRun : Set where
  run norun : ShouldRun

defaultTo : {A : Set} (x : A) → ShouldRun → Term → TC ⊤
defaultTo _ norun _    = typeError (strErr "Should not run!" ∷ [])
defaultTo x run   hole = bindTC (quoteTC x) (unify hole)

record Class (r : ShouldRun) : Set where
  constructor con
  field
    x : Bool
    @(tactic defaultTo x r) {y} : Bool
open Class

-- # Cases where the tactic should run

test₁ test₂ test₃ : Class run
test₁    = con true             -- Constructor application
test₂    = record { x = true }  -- Record construction
test₃ .x = true                 -- Missing copattern clause

_ = check test₁ == con true {true}
      and test₂ == con true {true}
      and test₃ == con true {true}

-- More elaborate missing copatterns
test₃′ : List Bool → Class run
test₃′ []      .x = false
test₃′ []      .y = true
test₃′ (b ∷ _) .x = b

_ =
  check test₃′ []             == con false {true}
    and λ b → test₃′ (b ∷ []) == con b {b}

-- # Cases where the tactic should not run

-- ## Giving the field explicitly

test₄ test₅ : Class norun
test₄ = con true {_}              is c such-that refl proves c .y ≡ false
test₅ = record{ x = true; y = _ } is c such-that refl proves c .y ≡ false

_ = check test₄ == con true {false}
      and test₅ == con true {false}

-- ## Eta-expansion

-- Eta-expansion of record metas should *not* trigger the tactic, since that
-- would make eta-expansion potentially lose solutions. For instance,
-- `con true {false} == _1`. Here solving `_1 := con true {false}` is valid, but
-- eta-expanding to `con _2 {_3}` and running `defaultTo _2 _3` leads to an error.

test₆ : Class norun
test₆ =
  _ is c such-that refl proves c .x ≡ true
    is c such-that refl proves c .y ≡ false

check₆ : test₆ ≡ con true {false}
check₆ = refl
