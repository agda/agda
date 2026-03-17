{-# OPTIONS --guardedness #-}
-- {-# OPTIONS -v tc.check.term.con:40 #-}
-- {-# OPTIONS -v tc.polarity:10 -v tc.with:0 -v tc.with.top:15 -v tc.with.strip:0 #-}

module InductiveAndCoinductiveConstructors where

open import Common.Coinduction

record ⊤ : Set where

data _×_ (A : Set) (B : Set) : Set where
  _,_ : (x : A) (y : B) → A × B

infixr 5 _≺_

data Stream (A : Set) : Set where
  _≺_ : (x : A) (xs : ∞ (Stream A)) → Stream A

data U : Set where
  stream : (a : U) → U
  _⊗_    : (a b : U) → U
  unit   : U

El : U → Set
El (stream a) = Stream (El a)
El (a ⊗ b)    = El a × El b
El unit       = ⊤

mutual

  data WHNF : U → Set where
    _≺_  : ∀ {a} → El a → Prog (stream a) → WHNF (stream a)
    _,_  : ∀ {a b} → WHNF a → WHNF b → WHNF (a ⊗ b)

  data Prog : U → Set where
    ↓_  : ∀ {a} → ∞ (WHNF a) → Prog a
    fst : ∀ {a b} → Prog (a ⊗ b) → Prog a
    snd : ∀ {a b} → Prog (a ⊗ b) → Prog b
    lab : Prog (stream unit) → Prog (stream (stream unit)) →
          Prog (stream unit ⊗ stream (stream unit))

whnf : ∀ {a} → Prog a → WHNF a
whnf (↓ w) = ♭ w
whnf (fst p) with whnf p
... | (x , y) = x
whnf (snd p) with whnf p
... | (x , y) = y
whnf (lab xs lss) with whnf xs | whnf lss
... | _ ≺ xs′ | (x ≺ ls) ≺ lss′ =
  ((_ ≺ fst (lab xs′ lss′)) , (♭ ls ≺ snd (lab xs′ lss′)))

⟦_⟧ : Prog (stream unit) → Stream ⊤
⟦ p ⟧ with whnf p
... | x ≺ xs = x ≺ ♯ ⟦ xs ⟧

data _≈_ : Stream ⊤ → Stream ⊤ → Set where
  cons : ∀ {xs xs′} → ∞ ((♭ xs) ≈ (♭ xs′)) → (_ ≺ xs) ≈ (_ ≺ xs′)

lemma : ∀ xs lss → ⟦ fst (lab xs lss) ⟧ ≈ ⟦ xs ⟧
lemma xs lss with whnf xs | whnf lss
... | _ ≺ xs′ | (x ≺ ls) ≺ lss′ = cons (♯ lemma xs′ lss′)

{- Andreas, 2012-09-07 WAS:
label : Prog (stream unit) → Stream ⊤ →
        Prog (stream unit ⊗ stream (stream unit))
label xs ls = lab xs (↓ (♯ (ls ≺ snd (label xs ls))))

shape-preserved : ∀ xs ls → ⟦ fst (label xs ls) ⟧ ≈ ⟦ xs ⟧
shape-preserved xs ls = lemma xs _
-- however, the solution for _ is not unique (see Issue 691)
-}

mutual
  label : Prog (stream unit) → Stream ⊤ →
          Prog (stream unit ⊗ stream (stream unit))
  label xs ls = lab xs (lss xs ls)

  lss   : Prog (stream unit) → Stream ⊤ → _
  lss   xs ls = ↓ (♯ (ls ≺ snd (label xs ls)))

shape-preserved : ∀ xs ls → ⟦ fst (label xs ls) ⟧ ≈ ⟦ xs ⟧
shape-preserved xs ls = lemma xs (lss xs ls)
