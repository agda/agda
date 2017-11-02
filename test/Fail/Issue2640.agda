{-# OPTIONS --experimental-irrelevance  #-}
--{-# OPTIONS -v tc.lhs.unify:65 -v tc.irr:50 #-}
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

data D : ..(b : Bool) → Set where
  c : (b : Bool) → D b

test : ..(a : Bool) → D a → Bool
test a (c b) = b

data ⊥ : Set where
record ⊤ : Set where constructor tt

case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x

-- Not so shape-irrelevant type!
T : ..(n : Bool) → Set
T n = case test n (c _) of λ where
        true  → ⊤
        false → ⊥

data Foo : Set where
  foo : .(b : Bool) → T b → Foo

bad : (b : ⊥) → foo true tt ≡ foo false b → ⊥
bad b _ = b

jackpot : ⊥
jackpot = bad _ refl
