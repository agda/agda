
data _≡_ {X : Set} : X → X → Set where
  refl : {x : X} → x ≡ x

ap : {X Y : Set} (f : X → Y) {x x' : X} → x ≡ x' → f x ≡ f x'
ap f refl = refl

_∙_ : {X : Set} {x y z : X} → x ≡ y → y ≡ z → x ≡ z
p ∙ refl = p

f : {X : Set} {x : X} {A : X → Set} (η θ : (y : X) → x ≡ y → A y)
  → η x refl ≡ θ x refl → ∀ y p → η y p ≡ θ y p
f η θ q y refl = ap (λ a → a) q

succeeds : (X : Set) (z t : X) (r : z ≡ t)
         → (λ (x y : X) (p : x ≡ y) (q : y ≡ z) → (p ∙ q) ∙ r)
         ≡ (λ (x y : X) (p : x ≡ y) (q : y ≡ z) → p ∙ (q ∙ r))
succeeds X z = f -- {A = λ - → (x y : X) (p : x ≡ y) (q : y ≡ z) → x ≡ - }
                (λ z r x y p q → (p ∙ q) ∙ r)
                (λ z r x y p q → p ∙ (q ∙ r))
                refl

fails : (X : Set) (z t : X) (r : z ≡ t)
      → (λ (x y : X) (p : x ≡ y) (q : y ≡ z) → (p ∙ q) ∙ r)
      ≡ (λ (x y : X) (p : x ≡ y) (q : y ≡ z) → p ∙ (q ∙ r))
fails X z t = f -- {A = λ - → (x y : X) (p : x ≡ y) (q : y ≡ z) → x ≡ - }
               (λ z r x y p q → (p ∙ q) ∙ r)
               (λ z r x y p q → p ∙ (q ∙ r))
               refl
               t
