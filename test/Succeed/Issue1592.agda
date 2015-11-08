-- Andreas, 2015-06-29, issue reported by Nisse

-- {-# OPTIONS -v tc.polarity:20 -v tc.pos:10 #-}
-- {-# OPTIONS -v tc.conv.elim:25 --show-implicit #-}

data ⊥ : Set where

data _≡_ {a} {A : Set a} : A → A → Set a where
  refl : ∀ x → x ≡ x

subst : ∀ {a p} {A : Set a} (P : A → Set p) {x y : A} →
        x ≡ y → P x → P y
subst P (refl x) p = p

record _∼_ (A B : Set₁) : Set₁ where
  field
    to               : A → B
    from             : B → A
    right-inverse-of : ∀ x → x ≡ to (from x)

mutual

  record R (c : ⊥) : Set₂ where
    field
      P : F c → Set₁
      Q : {I J : F c} → S c I J → P I → P J → Set₁

    Q′ : ∀ {I J} → S c I J → P I → P J → Set₁
    Q′ s x y = subst P (_∼_.to (S∼≡ c) s) x ≡ y

    field

      Q∼Q′ : ∀ {I J} (s : S c I J) {x y} → Q s x y ∼ Q′ s x y

  F : ⊥ → Set₁
  F ()

  S : (c : ⊥) → F c → F c → Set₁
  S ()

  S∼≡ : (c : ⊥) {I J : F c} → S c I J ∼ (I ≡ J)
  S∼≡ ()

s : ∀ c I → S c I I
s c I = _∼_.from (S∼≡ c) (refl I)

q : ∀ c e I x → R.Q e (s c I) x x
q c e I x =
  _∼_.from (R.Q∼Q′ e (s c I))
           (subst (λ eq → subst (R.P e) eq x ≡ x)
                  (_∼_.right-inverse-of (S∼≡ c) (refl I))
                  (refl x))

-- ERROR WAS (due to faulty positivity analysis for projections):
-- An internal error has occurred. Please report this as a bug.
-- Location of the error: src/full/Agda/TypeChecking/Conversion.hs:770
