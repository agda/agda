open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

data Foo (A : Set) (a : A) : Set where
  mk : (b : A) → Foo A a

Foo′ : (A : Set) → A → Set
Foo′ A a = Foo A a

-- This doesn't work: Foo has polarity [*, +], so the conversion checker
-- does actually look at the second argument
-- _ : Foo Nat 0 ≡ Foo Nat 1
-- _ = refl

-- But Foo′ has polarity [*, _] for some reason, so, with
-- lossy-unification, the following is accepted:
_ : Foo′ Nat 0 ≡ Foo′ Nat 1
_ = refl
