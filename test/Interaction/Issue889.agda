-- Andreas, 2013-09-17 catches a bug in constraint solving
-- with meta-variables applied to underapplied record constructors
-- {-# OPTIONS --show-implicit -v tc.meta.assign:50 -v tc.conv.elim:30 #-}
module Issue889 where

record Monad (M : Set → Set) : Set₁ where
  field
    return : ∀ {A} → A → M A
    _>>=_  : ∀ {A} {B : M A → Set} (m : M A) →
             ((x : A) → M (B (return x))) → M (B m)

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

_×_ : (A B : Set) → Set
A × B = Σ A λ _ → B

State : Set → Set → Set
State S X = S → X × S

-- Here is the underapplied record constructor
-- (made underapplied by eta-contraction, resp.).
state-return : ∀ {S X} → X → State S X
state-return x = _,_ x -- λ s → x , s

-- When giving the @_>>=_@ function to the record goal we get:
--
-- An internal error has occurred. Please report this as a bug.
-- Location of the error: src/full/Agda/TypeChecking/Conversion.hs:524
state-monad : ∀ {S} → Monad (State S)
state-monad {S} = record { return = state-return; _>>=_ = {!_>>=_!} }
  where
  postulate
    _>>=_ : ∀ {A} {B : State S A → Set} (m : State S A) →
          ((x : A) → State S (B (state-return x))) → State S (B m)
-- Bug arises when checking
--   _B (state-return x) = B (state-return x)
--   _B (_,_ x)          = B (_,_ x)
-- then Agda does something special for record constructors
-- [Miller unification in the presence of records]
-- (now only done for FULLY APPLIED record constructors!)
-- and produces some garbage solution for _B.

------------------------------------------------------------------------

-- Note that if we define the product type using data instead of
-- record then it works:

data _×′_ (A B : Set) : Set where
  _,_ : A → B → A ×′ B

State′ : Set → Set → Set
State′ S X = S → X ×′ S

state-return′ : ∀ {S X} → X → State′ S X
state-return′ x = λ s → x , s

state-monad′ : ∀ {S} → Monad (State′ S)
state-monad′ {S} = record { return = state-return′; _>>=_ = _>>=_ }
  where
  postulate
    _>>=_ : ∀ {A} {B : State′ S A → Set} (m : State′ S A) →
          ((x : A) → State′ S (B (state-return′ x))) → State′ S (B m)
