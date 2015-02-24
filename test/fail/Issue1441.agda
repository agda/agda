-- 2015-02-24 Andrea Vezzosi

-- Since type constructors are considered injective by the forcing analysis we are able to define the type for the "russel" paradox:

open import Common.Product

Type = Set₁

data Box : Type -> Set where

-- The following type should be rejected, as A is not forced.
data Tree' : Set -> Type where
  sup' : ∀ (A : Type) -> (A → ∃ Tree') → Tree' (Box A)

Tree = ∃ Tree'

sup : (a : Type) -> (f : a -> Tree) -> Tree
sup a f = _ , sup' a f

a : Tree -> Type
a (._ , sup' a _) = a

f : (t : Tree) -> a t -> Tree
f (._ , sup' a f) = f

-- The rest is the standard paradox

open import Common.Equality
open import Common.Prelude

normal : Tree -> Type
normal t = Σ (a t) (λ (y : a t) → (f t y ≡ sup (a t) (f t))) -> ⊥

nt : Type
nt = Σ Tree \ (t : Tree) -> normal t

p : nt -> Tree
p (x , _) = x

q : (y : nt) -> normal (p y)
q (x , y) = y

r : Tree
r = sup nt p

lemma : normal r
lemma ((y1 , y2) , z) = y2 (subst (\ y3 -> Σ _ \ (y : a y3) ->  f y3 y ≡ sup (a y3) (f y3)) (sym z) ((y1 , y2) , z))

russel : ⊥
russel = lemma ((r , lemma) , refl)

