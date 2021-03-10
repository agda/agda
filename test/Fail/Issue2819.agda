
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

data Irr (A : Set) : Set where
  irr : .(x : A) → Irr A

data D {A : Set} : Irr A → Set where
  -- x is mistakenly marked as forced here!
  d : (x : A) → D (irr x)

unD : ∀ {A : Set}{i} → D i → A
unD (d x) = x

dtrue=dfalse : d true ≡ d false
dtrue=dfalse = refl

_$≡_ : ∀ {A B : Set} (f : A → B) {x y} → x ≡ y → f x ≡ f y
f $≡ refl = refl

true=false : true ≡ false
true=false = unD $≡ dtrue=dfalse

data ⊥ : Set where

loop : ⊥
loop with true=false
... | ()
