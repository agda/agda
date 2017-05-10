-- Example by Simon Huber

{-# OPTIONS --without-K #-}

data _≡_ {A : Set} (a : A) : A → Set where
  refl : a ≡ a

ap : {A B : Set} (f : A → B) {a b : A} (p : a ≡ b) → f a ≡ f b
ap f refl = refl

-- \bub
_•_ : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
p • refl = p

infixr 30 _•_

! : {A : Set} {a b : A} → a ≡ b → b ≡ a
! refl = refl

-- \.  (NB: not • aka \bub)
_∙_ : {A : Set} {B : A → Set}
      {f g : (a : A) → B a} →
      f ≡ g →
      (x : A) → f x ≡ g x
refl ∙ x = refl

infix 30 _∙_

dotap : {A B : Set} {f g : A → B}
        (p : f ≡ g) (x : A)
      → p  ∙ x ≡ ap (λ F → F x) p
dotap refl x = refl

apcomp : {A B C : Set} (f : B → C) (g : A → B)
         {x y : A} (p : x ≡ y)
       → ap (λ a → f (g a)) p ≡ ap f (ap g p)
apcomp f g refl = refl

-- combinators for equality reasoning
_≡⟨_⟩_ : {A : Set} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩ q = p • q

infixr 2 _≡⟨_⟩_

_□ : {A : Set} (x : A) → x ≡ x
x □ = refl

module Wrong (A B : Set) (a0 : A) where
  const : B → (A → B)
  const = λ x _ → x

  to : {x y : B} → x ≡ y → const x ≡ const y
  to = ap const

  from : {x y : B} → const x ≡ const y → x ≡ y
  from = ap (λ F → F a0)

  -- This lemma should not typecheck:
  lem : {x y : B} (p : const x ≡ const y) (a : A)
      → p ∙ a ≡ to (from p) ∙ a
  lem p a = p ∙ a
            ≡⟨ dotap p a ⟩
            ap (λ F → F a) p
            ≡⟨ refl ⟩
            ap (λ F → const (F a) a) p
            ≡⟨ apcomp _ _ p ⟩
            ap (λ G → G a) (ap (λ F → const (F a)) p)
            ≡⟨ ap (ap (λ G → G a)) (apcomp const (λ F → F a) p) ⟩
            ap(λ G → G a) (ap const (ap (λ (F : A → B) → F a) p))
            ≡⟨ ! (dotap (ap const (ap (λ F → F a) p)) a) ⟩
            (to (from p) ∙ a) □
