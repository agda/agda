-- Example by Ian Orton

{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

_∧_ : Bool → Bool → Bool
true ∧ y = y
false ∧ y = false

data ⊥ : Set where

⊥-elim : ∀ {a} {A : Set a} → ⊥ → A
⊥-elim ()

¬_ : ∀ {a} → Set a → Set a
¬ A = A → ⊥

contradiction : ∀ {a b} {A : Set a} {B : Set b} → A → ¬ A → B
contradiction a f = ⊥-elim (f a)

_≢_ : ∀ {a} {A : Set a} (x y : A) → Set a
x ≢ y = ¬ (x ≡ y)

obvious : (b b' : Bool) (p : b ≢ b') → (b ∧ b') ≡ false
obvious false b'    notEq = refl
obvious true  false notEq = refl
obvious true  true  notEq = contradiction refl notEq

{-# BUILTIN REWRITE _≡_ #-}
{-# REWRITE obvious #-}

oops : (b : Bool) → b ∧ b ≡ false
oops b = refl

true≢false : true ≡ false → ⊥
true≢false ()

bot : ⊥
bot = true≢false (oops true)
