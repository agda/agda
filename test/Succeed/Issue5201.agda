open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Agda.Primitive

infixr 2 _×_

_×_ : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
A × B = Σ A λ _ → B

∃-notation exists-notation :
  ∀ {a b} {A : Set a} → (A → Set b) → Set (a ⊔ b)
∃-notation      = Σ _
exists-notation = Σ _

Σ-notation : ∀ {a b} (A : Set a) → (A → Set b) → Set (a ⊔ b)
Σ-notation = Σ

infixr 2 ∃-notation exists-notation Σ-notation

syntax ∃-notation (λ x → B)      = ∃ x × B
syntax exists-notation (λ x → B) = exists x × B
syntax Σ-notation A (λ x → B)    = [ x ∶ A ] × B

_ : ∃ b × b ≡ true × Bool
_ = true , refl , false

_ : exists b × b ≡ true
_ = true , refl

_ : [ b ∶ Bool ] × b ≡ true
_ = true , refl

_ : [ b₁ ∶ Bool ] × [ b₂ ∶ Bool ] × b₁ ≡ b₂
_ = true , true , refl

_ : [ b₁ ∶ Bool ] × ∃ b₂ × b₁ ≡ b₂
_ = true , true , refl

_ : [ f ∶ (Bool → Bool) ] × f ≡ λ x → x
_ = (λ x → x) , refl

data List (A : Set) : Set where
  []   : List A
  cons : A → List A → List A

infixr 5 cons

syntax []        = [ ]
syntax cons x xs = x consed to xs

_ : List Bool
_ = true consed to false consed to [ ]

f : List Bool → Bool
f [ ]                               = true
f (true consed to [ ])              = false
f (false consed to x consed to [ ]) = x
f _                                 = true
