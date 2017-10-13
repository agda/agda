------------------------------------------------------------------------
-- The Agda standard library
--
-- Transitive closures
------------------------------------------------------------------------

module Data.Plus where

open import Function
open import Function.Equivalence as Equiv using (_⇔_)
open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

------------------------------------------------------------------------
-- Transitive closure

infix 4 Plus

syntax Plus R x y = x [ R ]⁺ y

data Plus {a ℓ} {A : Set a} (_∼_ : Rel A ℓ) : Rel A (a ⊔ ℓ) where
  [_]     : ∀ {x y} (x∼y : x ∼ y) → x [ _∼_ ]⁺ y
  _∼⁺⟨_⟩_ : ∀ x {y z} (x∼⁺y : x [ _∼_ ]⁺ y) (y∼⁺z : y [ _∼_ ]⁺ z) →
            x [ _∼_ ]⁺ z

module _ {a ℓ} {A : Set a} {_∼_ : Rel A ℓ} where

 []-injective : ∀ {x y p q} → (x [ _∼_ ]⁺ y ∋ [ p ]) ≡ [ q ] → p ≡ q
 []-injective refl = refl

 ∼⁺⟨⟩-injectiveˡ : ∀ {x y z} {p r : x [ _∼_ ]⁺ y} {q s} →
                   (x [ _∼_ ]⁺ z ∋ x ∼⁺⟨ p ⟩ q) ≡ (x ∼⁺⟨ r ⟩ s) → p ≡ r
 ∼⁺⟨⟩-injectiveˡ refl = refl

 ∼⁺⟨⟩-injectiveʳ : ∀ {x y z} {p r : x [ _∼_ ]⁺ y} {q s} →
                   (x [ _∼_ ]⁺ z ∋ x ∼⁺⟨ p ⟩ q) ≡ (x ∼⁺⟨ r ⟩ s) → q ≡ s
 ∼⁺⟨⟩-injectiveʳ refl = refl


-- "Equational" reasoning notation. Example:
--
--   lemma =
--     x  ∼⁺⟨ [ lemma₁ ] ⟩
--     y  ∼⁺⟨ lemma₂ ⟩∎
--     z  ∎

finally : ∀ {a ℓ} {A : Set a} {_∼_ : Rel A ℓ} x y →
          x [ _∼_ ]⁺ y → x [ _∼_ ]⁺ y
finally _ _ = id

syntax finally x y x∼⁺y = x ∼⁺⟨ x∼⁺y ⟩∎ y ∎

infixr 2 _∼⁺⟨_⟩_
infix  3 finally

-- Map.

map : ∀ {a a′ ℓ ℓ′} {A : Set a} {A′ : Set a′}
        {_R_ : Rel A ℓ} {_R′_ : Rel A′ ℓ′} {f : A → A′} →
      _R_ =[ f ]⇒ _R′_ → Plus _R_ =[ f ]⇒ Plus _R′_
map R⇒R′ [ xRy ]             = [ R⇒R′ xRy ]
map R⇒R′ (x ∼⁺⟨ xR⁺z ⟩ zR⁺y) =
  _ ∼⁺⟨ map R⇒R′ xR⁺z ⟩ map R⇒R′ zR⁺y

------------------------------------------------------------------------
-- Alternative definition of transitive closure

-- A generalisation of Data.List.Nonempty.List⁺.

infixr 5 _∷_ _++_
infix  4 Plus′

syntax Plus′ R x y = x ⟨ R ⟩⁺ y

data Plus′ {a ℓ} {A : Set a} (_∼_ : Rel A ℓ) : Rel A (a ⊔ ℓ) where
  [_] : ∀ {x y} (x∼y : x ∼ y) → x ⟨ _∼_ ⟩⁺ y
  _∷_ : ∀ {x y z} (x∼y : x ∼ y) (y∼⁺z : y ⟨ _∼_ ⟩⁺ z) → x ⟨ _∼_ ⟩⁺ z

-- Transitivity.

_++_ : ∀ {a ℓ} {A : Set a} {_∼_ : Rel A ℓ} {x y z} →
       x ⟨ _∼_ ⟩⁺ y → y ⟨ _∼_ ⟩⁺ z → x ⟨ _∼_ ⟩⁺ z
[ x∼y ]      ++ y∼⁺z = x∼y ∷ y∼⁺z
(x∼y ∷ y∼⁺z) ++ z∼⁺u = x∼y ∷ (y∼⁺z ++ z∼⁺u)

-- Plus and Plus′ are equivalent.

equivalent : ∀ {a ℓ} {A : Set a} {_∼_ : Rel A ℓ} {x y} →
             Plus _∼_ x y ⇔ Plus′ _∼_ x y
equivalent {_∼_ = _∼_} = Equiv.equivalence complete sound
  where
  complete : Plus _∼_ ⇒ Plus′ _∼_
  complete [ x∼y ]             = [ x∼y ]
  complete (x ∼⁺⟨ x∼⁺y ⟩ y∼⁺z) = complete x∼⁺y ++ complete y∼⁺z

  sound : Plus′ _∼_ ⇒ Plus _∼_
  sound [ x∼y ]      = [ x∼y ]
  sound (x∼y ∷ y∼⁺z) = _ ∼⁺⟨ [ x∼y ] ⟩ sound y∼⁺z
