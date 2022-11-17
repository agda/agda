open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma

-- The option --unicode-sigma can not be used in OPTIONS pragmas, but
-- it can be used in .agda-lib files. When this option is used, then
-- the notation × is built-in.

_ : Bool × Bool
_ = true , false

-- It desugars to the builtin Σ-type. The type from Agda.Builtin.Sigma
-- is called Σ̂.

_ : (Bool × Bool) ≡ Σ̂ Bool (λ _ → Bool)
_ = refl

-- An ASCII-only variant is also supported: (x). This variant is
-- available even if --unicode-sigma is not used.

_ : Bool (x) Bool
_ = true , false

-- One can use multiple binders to the left of ×. Sequences of
-- Σ-bindings are translated to right-nested Σ-types.

_ : (A B : Set) (C : Set → Set) × A × B
_ = Bool , Bool , (λ _ → Bool) , true , false

-- One can also use a notation with Σ. This notation allows the use of
-- domain-free binders, like ∀ does. (However, hidden arguments and
-- attributes are not allowed.)

_ : Σ A B (C : Set → Set) × A × B
_ = Bool , Bool , (λ _ → Bool) , true , false

-- Again there is an ASCII-only variant, which is also available even
-- if --unicode-sigma is not used. This variant is not capitalised, to
-- match the keyword forall, and so that one can still use the name
-- Sigma (for instance in the module name Agda.Builtin.Sigma).

_ : sigma A B (C : Set → Set) × A × B
_ = Bool , Bool , (λ _ → Bool) , true , false

-- One can use certain patterns in the domains of Σ-types.

_ : (p@(x , _) : Bool × Bool) × x ≡ p .snd
_ = (true , true) , refl

-- Σ-types bind stronger than Π-types, but weaker than many other
-- things.

_ : Bool × Bool → Bool
_ = fst

_ : (_ : Bool × Bool) → Bool
_ = snd

_ : (_ : Bool) × Bool → Bool
_ = fst

_ : Σ (_ : Bool) × Bool → Bool
_ = snd

_ : (F : Set → Set) × F ≡ (λ A → A) × Bool
_ = _ , refl , true

_ : (F : Set → Set) × F ≡ λ A → A × Bool
_ = _ , refl
