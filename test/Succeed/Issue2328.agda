{- Examples by Twan van Laarhoven -}

{-# OPTIONS --rewriting --confluence-check #-}
module _ where

open import Agda.Builtin.Equality
{-# BUILTIN REWRITE _≡_ #-}

const : ∀ {a b} {A : Set a} {B : Set b} → A → B → A
const x _ = x

_∘_ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c}
    → (f : ∀ {x} (y : B x) → C y) (g : (x : A) → B x)
    → (x : A) → C (g x)
(f ∘ g) x = f (g x)

postulate M : Set → Set
postulate pure : ∀ {A} → A → M A
postulate _>>=_ : ∀ {A B} → M A → (A → M B) → M B
postulate bind-assoc : ∀ {A B C mx} {my : A → M B} {mz : B → M C} → (mx >>= my) >>= mz  ≡  mx >>= \x → my x >>= mz
{-# REWRITE bind-assoc #-}

_<*>_ : ∀ {A B} → M (A → B) → M A → M B
mf <*> mx = mf >>= \f → mx >>= (pure ∘ f)

-- Agda was comparing inferred relevances here, causing the rewrite rule
-- to fail.
shouldWork : ∀ {A B} (mx : M A) (my : M B)
  → (mx >>= (pure ∘ const)) <*> my
  ≡ (mx >>= (pure ∘ const)) >>= (\f → my >>= (pure ∘ f))
shouldWork mx my = refl

shouldAlsoWork  : ∀ {A B} (mx : M A) (my : M B)
  → (mx >>= (pure ∘ const)) <*> my
  ≡ (mx >>= (pure ∘ \x _ → x)) >>= (\f → my >>= (pure ∘ f))
shouldAlsoWork mx my = refl

shouldAlsoWork2  : ∀ {A B} (mx : M A) (my : M B)
  → (mx >>= (pure ∘ const)) >>= (\f → my >>= (pure ∘ f))
  ≡ (mx >>= (pure ∘ \x _ → x)) >>= (\f → my >>= (pure ∘ f))
shouldAlsoWork2 mx my = refl
