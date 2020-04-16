open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Agda.Builtin.Reflection
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit

id : {A : Set} → A → A
id x = x

if_then_else_ : {A : Set} → Bool → A → A → A
if true  then x else y = x
if false then x else y = y

not : Bool → Bool
not = if_then false else true

quote-list : List Bool → TC (List (Arg Term))
quote-list []       = returnTC []
quote-list (b ∷ bs) =
  bindTC (quoteTC b) λ b →
  bindTC (quote-list bs) λ bs →
  returnTC (arg (arg-info visible relevant) b ∷ bs)

macro

  apply′ : Term → Term → List Bool → Term → TC ⊤
  apply′ t f xs goal =
    bindTC (quote-list xs) λ bs →
    bindTC (apply t f bs) λ (type , term) →
    bindTC (checkType term type) λ _ →
           unify goal term

b₁ : Bool
b₁ = apply′ (Bool → Bool) not (false ∷ [])

_ : b₁ ≡ true
_ = refl

b₂ : Bool
b₂ = apply′ ({A : Set} → A → A) id (false ∷ [])

_ : b₂ ≡ false
_ = refl

b₃ : Bool
b₃ = apply′ (Bool → Bool) (id {A = Bool}) (false ∷ [])

_ : b₃ ≡ false
_ = refl

b₄ : Bool
b₄ = apply′ (Bool → Bool → Bool → Bool) if_then_else_
            (false ∷ true ∷ false ∷ [])

_ : b₄ ≡ false
_ = refl
