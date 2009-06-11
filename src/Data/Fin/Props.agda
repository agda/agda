------------------------------------------------------------------------
-- Properties related to Fin, and operations making use of these
-- properties (or other properties not available in Data.Fin)
------------------------------------------------------------------------

module Data.Fin.Props where

open import Data.Fin
open import Data.Nat as N
  using (ℕ; zero; suc; s≤s; z≤n)
  renaming (_≤_ to _ℕ≤_; _<_ to _ℕ<_; _+_ to _ℕ+_)
open N.≤-Reasoning
import Data.Nat.Properties as N
open import Data.Function
open import Relation.Nullary
open import Relation.Unary
open import Relation.Binary
open import Relation.Binary.FunctionSetoid
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; cong; subst)
open import Category.Functor
open import Category.Applicative

------------------------------------------------------------------------
-- Properties

private
  drop-suc : ∀ {o} {m n : Fin o} →
             suc m ≡ (Fin (suc o) ∶ suc n) → m ≡ n
  drop-suc refl = refl

preorder : ℕ → Preorder
preorder n = PropEq.preorder (Fin n)

setoid : ℕ → Setoid
setoid n = PropEq.setoid (Fin n)

strictTotalOrder : ℕ → StrictTotalOrder
strictTotalOrder n = record
  { carrier            = Fin n
  ; _≈_                = _≡_
  ; _<_                = _<_
  ; isStrictTotalOrder = record
    { isEquivalence = PropEq.isEquivalence
    ; trans         = N.<-trans
    ; compare       = cmp
    ; <-resp-≈      = PropEq.resp₂ _<_
    }
  }
  where
  cmp : ∀ {n} → Trichotomous _≡_ (_<_ {n})
  cmp zero    zero    = tri≈ (λ())     refl  (λ())
  cmp zero    (suc j) = tri< (s≤s z≤n) (λ()) (λ())
  cmp (suc i) zero    = tri> (λ())     (λ()) (s≤s z≤n)
  cmp (suc i) (suc j) with cmp i j
  ... | tri<  lt ¬eq ¬gt = tri< (s≤s lt)         (¬eq ∘ drop-suc) (¬gt ∘ N.≤-pred)
  ... | tri> ¬lt ¬eq  gt = tri> (¬lt ∘ N.≤-pred) (¬eq ∘ drop-suc) (s≤s gt)
  ... | tri≈ ¬lt  eq ¬gt = tri≈ (¬lt ∘ N.≤-pred) (cong suc eq)    (¬gt ∘ N.≤-pred)

decSetoid : ℕ → DecSetoid
decSetoid n = StrictTotalOrder.decSetoid (strictTotalOrder n)

infix 4 _≟_

_≟_ : {n : ℕ} → Decidable {Fin n} _≡_
_≟_ {n} = DecSetoid._≟_ (decSetoid n)

to-from : ∀ n → toℕ (fromℕ n) ≡ n
to-from zero    = refl
to-from (suc n) = cong suc (to-from n)

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

inject-lemma : ∀ {n} {i : Fin n} (j : Fin′ i) →
               toℕ (inject j) ≡ toℕ j
inject-lemma {i = zero}  ()
inject-lemma {i = suc i} zero    = refl
inject-lemma {i = suc i} (suc j) = cong suc (inject-lemma j)

inject+-lemma : ∀ m k → m ≡ toℕ (inject+ k (fromℕ m))
inject+-lemma zero    k = refl
inject+-lemma (suc m) k = cong suc (inject+-lemma m k)

inject₁-lemma : ∀ {m} (i : Fin m) → toℕ (inject₁ i) ≡ toℕ i
inject₁-lemma zero    = refl
inject₁-lemma (suc i) = cong suc (inject₁-lemma i)

inject≤-lemma : ∀ {m n} (i : Fin m) (le : m ℕ≤ n) →
                toℕ (inject≤ i le) ≡ toℕ i
inject≤-lemma zero    (N.s≤s le) = refl
inject≤-lemma (suc i) (N.s≤s le) = cong suc (inject≤-lemma i le)

≺⇒<′ : _≺_ ⇒ N._<′_
≺⇒<′ (n ≻toℕ i) = N.≤⇒≤′ (bounded i)

<′⇒≺ : N._<′_ ⇒ _≺_
<′⇒≺ {n} N.≤′-refl    = subst (λ i → i ≺ suc n) (to-from n)
                              (suc n ≻toℕ fromℕ n)
<′⇒≺ (N.≤′-step m≤′n) with <′⇒≺ m≤′n
<′⇒≺ (N.≤′-step m≤′n) | n ≻toℕ i =
  subst (λ i → i ≺ suc n) (inject₁-lemma i) (suc n ≻toℕ (inject₁ i))

------------------------------------------------------------------------
-- Operations

infixl 6 _+′_

_+′_ : ∀ {m n} (i : Fin m) (j : Fin n) → Fin (N.pred m ℕ+ n)
i +′ j = inject≤ (i + j) (N._+-mono_ (prop-toℕ-≤ i) ≤-refl)
  where open Poset N.poset renaming (refl to ≤-refl)

-- reverse {n} "i" = "n ∸ 1 ∸ i".

reverse : ∀ {n} → Fin n → Fin n
reverse {zero}  ()
reverse {suc n} i  = inject≤ (n ℕ- i) (N.n∸m≤n (toℕ i) (suc n))

-- If there is an injection from a set to a finite set, then equality
-- of the set can be decided.

eq? : ∀ {S n} →
      Injection S (PropEq.setoid (Fin n)) → Decidable (Setoid._≈_ S)
eq? inj x y with to ⟨$⟩ x ≟ to ⟨$⟩ y where open Injection inj
... | yes tox≡toy = yes (Injection.injective inj tox≡toy)
... | no  tox≢toy = no  (tox≢toy ∘ pres (Injection.to inj))

-- Quantification over finite sets commutes with applicative functors.

sequence : ∀ {F n} {P : Pred (Fin n)} → RawApplicative F →
           (∀ i → F (P i)) → F (∀ i → P i)
sequence {F} RA = helper _ _
  where
  open RawApplicative RA

  helper : ∀ n (P : Pred (Fin n)) → (∀ i → F (P i)) → F (∀ i → P i)
  helper zero    P ∀iPi = pure (λ())
  helper (suc n) P ∀iPi =
    combine <$> ∀iPi zero ⊛ helper n (λ n → P (suc n)) (∀iPi ∘ suc)
    where
    combine : P zero → (∀ i → P (suc i)) → ∀ i → P i
    combine z s zero    = z
    combine z s (suc i) = s i

private

  -- Included just to show that sequence above has an inverse (under
  -- an equivalence relation with two equivalence classes, one with
  -- all inhabited sets and the other with all uninhabited sets).

  sequence⁻¹ : ∀ {F A} {P : Pred A} → RawFunctor F →
               F (∀ i → P i) → ∀ i → F (P i)
  sequence⁻¹ RF F∀iPi i = (λ f → f i) <$> F∀iPi
    where open RawFunctor RF
