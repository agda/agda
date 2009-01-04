------------------------------------------------------------------------
-- Properties related to Fin, and operations making use of these
-- properties (or other properties not available in Data.Fin)
------------------------------------------------------------------------

module Data.Fin.Props where

open import Data.Fin
import Data.Nat as N
open N using (ℕ; zero; suc; s≤s; z≤n)
       renaming (_≤_ to _ℕ≤_; _<_ to _ℕ<_; _+_ to _ℕ+_)
open N.≤-Reasoning
import Data.Nat.Properties as N
open import Data.Function
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Properties

private
  drop-suc : ∀ {o} {m n : Fin o} →
             suc m ≡ (Fin (suc o) ∶ suc n) → m ≡ n
  drop-suc ≡-refl = ≡-refl

preorder : ℕ → Preorder
preorder n = ≡-preorder (Fin n)

setoid : ℕ → Setoid
setoid n = ≡-setoid (Fin n)

strictTotalOrder : ℕ → StrictTotalOrder
strictTotalOrder n = record
  { carrier            = Fin n
  ; _≈_                = _≡_
  ; _<_                = _<_
  ; isStrictTotalOrder = record
    { isEquivalence = ≡-isEquivalence
    ; trans         = N.<-trans
    ; compare       = cmp
    ; ≈-resp-<      = ≡-resp _<_
    }
  }
  where
  cmp : ∀ {n} → Trichotomous _≡_ (_<_ {n})
  cmp zero    zero    = tri≈ (λ())     ≡-refl (λ())
  cmp zero    (suc j) = tri< (s≤s z≤n) (λ())  (λ())
  cmp (suc i) zero    = tri> (λ())     (λ())  (s≤s z≤n)
  cmp (suc i) (suc j) with cmp i j
  ... | tri<  lt ¬eq ¬gt = tri< (s≤s lt)         (¬eq ∘ drop-suc) (¬gt ∘ N.≤-pred)
  ... | tri> ¬lt ¬eq  gt = tri> (¬lt ∘ N.≤-pred) (¬eq ∘ drop-suc) (s≤s gt)
  ... | tri≈ ¬lt  eq ¬gt = tri≈ (¬lt ∘ N.≤-pred) (≡-cong suc eq)  (¬gt ∘ N.≤-pred)

decSetoid : ℕ → DecSetoid
decSetoid n = StrictTotalOrder.decSetoid (strictTotalOrder n)

infix 4 _≟_

_≟_ : {n : ℕ} → Decidable {Fin n} _≡_
_≟_ {n} = DecSetoid._≟_ (decSetoid n)

bounded : ∀ {n} (i : Fin n) → toℕ i ℕ< n
bounded zero    = s≤s z≤n
bounded (suc i) = s≤s (bounded i)

prop-toℕ-≤ : ∀ {n} (x : Fin n) → toℕ x ℕ≤ N.pred n
prop-toℕ-≤ zero                 = z≤n
prop-toℕ-≤ (suc {n = zero}  ())
prop-toℕ-≤ (suc {n = suc n} i)  = s≤s (prop-toℕ-≤ i)

nℕ-ℕi≤n : ∀ n i → n ℕ-ℕ i ℕ≤ n
nℕ-ℕi≤n n       zero     = begin n ∎
nℕ-ℕi≤n zero    (suc ())
nℕ-ℕi≤n (suc n) (suc i)  = begin
  n ℕ-ℕ i ≤⟨ nℕ-ℕi≤n n i ⟩
  n       ≤⟨ N.n≤1+n n ⟩
  suc n   ∎

inject+-lemma : ∀ m k → m ≡ toℕ (inject+ k (fromℕ m))
inject+-lemma zero    k = ≡-refl
inject+-lemma (suc m) k = ≡-cong suc (inject+-lemma m k)

------------------------------------------------------------------------
-- Operations

infixl 6 _+′_

_+′_ : ∀ {m n} (i : Fin m) (j : Fin n) → Fin (N.pred m ℕ+ n)
i +′ j = inject≤ (i + j) (N._+-mono_ (prop-toℕ-≤ i) refl)
  where open Poset N.poset

-- reverse {n} "i" = "n ∸ 1 ∸ i".

reverse : ∀ {n} → Fin n → Fin n
reverse {zero}  ()
reverse {suc n} i  = inject≤ (n ℕ- i) (N.n∸m≤n (toℕ i) (suc n))

-- If there is an injection from a set to a finite set, then equality
-- of the set can be decided.

eq? : ∀ {A n} → Injection A (Fin n) → Decidable (_≡_ {A})
eq? inj x y with to x ≟ to y  where open Injection inj
... | yes tox≡toy = yes (Injection.injective inj tox≡toy)
... | no  tox≢toy = no  (tox≢toy ∘ ≡-cong (Injection.to inj))
