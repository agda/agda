
open import Agda.Builtin.Equality using (_≡_; refl)

record ∃ {A : Set} (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open ∃ public

uncurry : {A : Set} {B : A → Set} {C : ∃ B → Set₁} →
          ((x : A) (y : B x) → C (x , y)) →
          ((p : ∃ B) → C p)
uncurry f (x , y) = f x y

_⟶_ : {I : Set} → (I → Set) → (I → Set) → Set
A ⟶ B = ∀ {i} → A i → B i

postulate
  I   : Set
  i j : I
  R   : I → I → Set

record P : Set where
  field
    f : ∀ {k} → R i k → ∃ λ l → R k l

Q : Set
Q =
  ∃ λ (f : ∀ {j} → R i j → I) →
  (λ { (j , k) → ∃ λ (r : R i j) → f r ≡ k }) ⟶ uncurry R

to : P → Q
to f = (λ r → proj₁ (P.f f r))
     , λ { (r , refl) → proj₂ (P.f f r) }

from : Q → P
P.f (from (f , g)) r = f r , g (r , refl)

-- Should produce a nice error and not throw an __IMPOSSIBLE__.
to∘from : ∀ q → to (from q) ≡ q
to∘from _ = refl
