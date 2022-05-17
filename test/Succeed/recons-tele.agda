open import Agda.Builtin.Nat
open import Agda.Builtin.Unit
open import Agda.Builtin.Reflection renaming (bindTC to _>>=_)
open import Agda.Builtin.List
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality

infixr -1 _$_
_$_ : ∀ {a b}{A : Set a}{B : Set b} → (A → B) → A → B
f $ x = f x

map : ∀ {a b}{A : Set a}{B : Set b} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

reverse : ∀ {a}{A : Set a} → List A → List A
reverse {A = A} xs = reverseAcc xs []
  where
    reverseAcc : List A → List A → List A
    reverseAcc [] a = a
    reverseAcc (x ∷ xs) a = reverseAcc xs (x ∷ a)

data Fin : Nat → Set where
  zero : ∀ {n} → Fin (suc n)
  suc  : ∀ {n} → Fin n → Fin (suc n)

infixr 5 _∷_
data Vec {a} (A : Set a) : Nat → Set a where
  []  : Vec A zero
  _∷_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (suc n)

data Ix : (d : Nat) → (s : Vec Nat d) → Set where
  []   : Ix 0 []
  _∷_  : ∀ {d s x} → Fin x → (ix : Ix d s) → Ix (suc d) (x ∷ s)

record Ar {a} (X : Set a) (d : Nat) (s : Vec Nat d) : Set a where
  constructor imap
  field sel : Ix d s → X
open Ar public


foo : Nat → Nat
foo x = 1 + x

test-ar : ∀ {n} → (a : Ar Nat 1 (n ∷ [])) → Ar Nat 1 (n ∷ [])
test-ar (imap f) = imap λ iv → foo $ foo $ f iv

-- Make sure that the telescope is also reconstructed when
-- calling getDefinition with withReconstructed.
macro
  z : Name → Term → TC ⊤
  z n hole = do
    (function (clause tel ps t ∷ [])) ←
      withReconstructed $ getDefinition n
      where _ → quoteTC "ERROR" >>= unify hole
    t ← withReconstructed
        $ inContext (reverse tel)
        $ normalise t
    quoteTC t >>= unify hole


test₁ : z test-ar
      ≡ con (quote imap) (_ ∷ _ ∷ _ ∷ _ ∷
                          arg _ (lam _ (abs "iv"
                                        (con (quote Nat.suc) _)))
                          ∷ [])
test₁ = refl


-- Make sure that getType behaves correctly under withReconstructed.
macro
  q : Name → Term → TC ⊤
  q n hole = do
    t ← withReconstructed $
        getType n
    t ← withReconstructed $
        normalise t
    quoteTC t >>= unify hole

test₂ : Term
test₂ = q test-ar
