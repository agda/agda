-- A discussion from -- https://twitter.com/YuumuKonpaku/status/1052959340468953088
-- Andreas, 2019-08-18, test also #1346 (infix declaration in renaming)

module MdJustHighlightAgdaAsHtml where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Primitive public using (lzero)
  renaming (Level to ULevel; lsuc to lsucc; _⊔_ to infixl 42 _⊔_)

Type : (i : ULevel) -> Set (lsucc i)
Type i = Set i

data ⊥ : Type lzero where
pattern O = zero
pattern S n = (suc n)
variable i : ULevel

¬ : (A : Type i) → Type i
¬ A = A → ⊥
_≠_ : {A : Type i} → (A → A → Type i)
x ≠ y = ¬ (x ≡ y)

infix 10 _∨_
data _∨_ {a b} (A : Type a) (B : Type b) : Set (a ⊔ b) where
  a-intro : A -> A ∨ B
  b-intro : B -> A ∨ B

test : (x y : Nat) -> (x ≡ y) ∨ (x ≠ y)
test O O = a-intro refl
test O (S y) = b-intro (λ ())
test (S x) O = b-intro (λ ())
test (S x) (S y) with test x y
... | a-intro refl = a-intro refl
... | b-intro k = b-intro (lemma k)
  where
    lemma : {a b : Nat} -> a ≠ b -> S a ≠ S b
    lemma p refl = p refl
