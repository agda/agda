-- Andreas, 2015-05-02, issue reported by Gabe Dijkstra
open import Common.Prelude
open import Common.Equality

data T : Set where
  c0 : ⊥ → T
  c1 : ⊥ → T

-- The following should not pass, as c0 and c1 are not fully applied.
c0≠c1 : c0 ≡ c1 → ⊥
c0≠c1 ()

-- The latter conflicts with function extensionality.
postulate
  fun-ext : {A B : Set} → (f g : A → B) → ((x : A) → f x ≡ g x) → f ≡ g

c0=c1 : c0 ≡ c1
c0=c1 = fun-ext c0 c1 (λ ())

wrong : ⊥
wrong = c0≠c1 c0=c1
