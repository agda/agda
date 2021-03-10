
open import Agda.Primitive public

variable
 ℓ ℓ' : Level

data _≡_ {X : Set ℓ} : X → X → Set ℓ where
  refl : {x : X} → x ≡ x

ap : {X : Set ℓ} {Y : Set ℓ'} (f : X → Y) {x x' : X} → x ≡ x' → f x ≡ f x'
ap f refl = refl

_∙_ : {X : Set ℓ} {x y z : X} → x ≡ y → y ≡ z → x ≡ z
p ∙ refl = p

yoneda-elem-lc : {X : Set ℓ} {x : X} {A : X → Set ℓ'} (η θ : (y : X) → x ≡ y → A y)
               → η x refl ≡ θ x refl → ∀ y p → η y p ≡ θ y p
yoneda-elem-lc η θ q y refl = ap (λ a → a) q

ext-assoc : {X : Set ℓ} {z t : X} (r : z ≡ t)
          → (λ (x y : X) (p : x ≡ y) (q : y ≡ z) → (p ∙ q) ∙ r)
          ≡ (λ (x y : X) (p : x ≡ y) (q : y ≡ z) → p ∙ (q ∙ r))
ext-assoc {ℓ} {X} {z} {t} = yoneda-elem-lc
                            -- {A = λ - → (x y : X) (p : x ≡ y) (q : y ≡ z) → x ≡ - }
                            (λ z r x y p q → (p ∙ q) ∙ r)
                            (λ z r x y p q → p ∙ (q ∙ r))
                            refl
                            t
