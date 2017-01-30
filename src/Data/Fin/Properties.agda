------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to Fin, and operations making use of these
-- properties (or other properties not available in Data.Fin)
------------------------------------------------------------------------

module Data.Fin.Properties where

open import Algebra
open import Data.Fin
open import Data.Nat as N
  using (ℕ; zero; suc; s≤s; z≤n; _∸_)
  renaming (_≤_ to _ℕ≤_; _<_ to _ℕ<_; _+_ to _ℕ+_)
import Data.Nat.Properties as N
open import Data.Product
open import Function
open import Function.Equality as FunS using (_⟨$⟩_)
open import Function.Injection using (_↣_)
open import Algebra.FunctionProperties
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; refl; cong; subst)
open import Category.Functor
open import Category.Applicative

open DecTotalOrder N.decTotalOrder using () renaming (refl to ℕ≤-refl)

------------------------------------------------------------------------
-- Properties

suc-injective : ∀ {o} {m n : Fin o} → Fin.suc m ≡ suc n → m ≡ n
suc-injective refl = refl

preorder : ℕ → Preorder _ _ _
preorder n = P.preorder (Fin n)

setoid : ℕ → Setoid _ _
setoid n = P.setoid (Fin n)

cmp : ∀ {n} → Trichotomous _≡_ (_<_ {n})
cmp zero    zero    = tri≈ (λ())     refl  (λ())
cmp zero    (suc j) = tri< (s≤s z≤n) (λ()) (λ())
cmp (suc i) zero    = tri> (λ())     (λ()) (s≤s z≤n)
cmp (suc i) (suc j) with cmp i j
... | tri<  lt ¬eq ¬gt = tri< (s≤s lt)         (¬eq ∘ suc-injective) (¬gt ∘ N.≤-pred)
... | tri> ¬lt ¬eq  gt = tri> (¬lt ∘ N.≤-pred) (¬eq ∘ suc-injective) (s≤s gt)
... | tri≈ ¬lt  eq ¬gt = tri≈ (¬lt ∘ N.≤-pred) (cong suc eq)    (¬gt ∘ N.≤-pred)

strictTotalOrder : ℕ → StrictTotalOrder _ _ _
strictTotalOrder n = record
  { Carrier            = Fin n
  ; _≈_                = _≡_
  ; _<_                = _<_
  ; isStrictTotalOrder = record
    { isEquivalence = P.isEquivalence
    ; trans         = N.<-trans
    ; compare       = cmp
    }
  }


decSetoid : ℕ → DecSetoid _ _
decSetoid n = StrictTotalOrder.decSetoid (strictTotalOrder n)

infix 4 _≟_

_≟_ : {n : ℕ} → Decidable {A = Fin n} _≡_
_≟_ {n} = DecSetoid._≟_ (decSetoid n)

to-from : ∀ n → toℕ (fromℕ n) ≡ n
to-from zero    = refl
to-from (suc n) = cong suc (to-from n)

from-to : ∀ {n} (i : Fin n) → fromℕ (toℕ i) ≡ strengthen i
from-to zero    = refl
from-to (suc i) = cong suc (from-to i)

toℕ-strengthen : ∀ {n} (i : Fin n) → toℕ (strengthen i) ≡ toℕ i
toℕ-strengthen zero    = refl
toℕ-strengthen (suc i) = cong suc (toℕ-strengthen i)

toℕ-injective : ∀ {n} {i j : Fin n} → toℕ i ≡ toℕ j → i ≡ j
toℕ-injective {zero}  {}      {}      _
toℕ-injective {suc n} {zero}  {zero}  eq = refl
toℕ-injective {suc n} {zero}  {suc j} ()
toℕ-injective {suc n} {suc i} {zero}  ()
toℕ-injective {suc n} {suc i} {suc j} eq =
  cong suc (toℕ-injective (cong N.pred eq))

bounded : ∀ {n} (i : Fin n) → toℕ i ℕ< n
bounded zero    = s≤s z≤n
bounded (suc i) = s≤s (bounded i)

prop-toℕ-≤ : ∀ {n} (i : Fin n) → toℕ i ℕ≤ N.pred n
prop-toℕ-≤ zero                 = z≤n
prop-toℕ-≤ (suc {n = zero}  ())
prop-toℕ-≤ (suc {n = suc n} i)  = s≤s (prop-toℕ-≤ i)

-- A simpler implementation of prop-toℕ-≤,
-- however, with a different reduction behavior.
-- If no one needs the reduction behavior of prop-toℕ-≤,
-- it can be removed in favor of prop-toℕ-≤′.
prop-toℕ-≤′ : ∀ {n} (i : Fin n) → toℕ i ℕ≤ N.pred n
prop-toℕ-≤′ i = N.<⇒≤pred (bounded i)

-- Lemma:  n - i ≤ n.
nℕ-ℕi≤n : ∀ n i → n ℕ-ℕ i ℕ≤ n
nℕ-ℕi≤n n       zero     = ℕ≤-refl
nℕ-ℕi≤n zero    (suc ())
nℕ-ℕi≤n (suc n) (suc i)  = begin
  n ℕ-ℕ i  ≤⟨ nℕ-ℕi≤n n i ⟩
  n        ≤⟨ N.n≤1+n n ⟩
  suc n    ∎
  where open N.≤-Reasoning

inject-lemma : ∀ {n} {i : Fin n} (j : Fin′ i) →
               toℕ (inject j) ≡ toℕ j
inject-lemma {i = zero}  ()
inject-lemma {i = suc i} zero    = refl
inject-lemma {i = suc i} (suc j) = cong suc (inject-lemma j)

inject+-lemma : ∀ {m} n (i : Fin m) → toℕ i ≡ toℕ (inject+ n i)
inject+-lemma n zero    = refl
inject+-lemma n (suc i) = cong suc (inject+-lemma n i)

inject₁-lemma : ∀ {m} (i : Fin m) → toℕ (inject₁ i) ≡ toℕ i
inject₁-lemma zero    = refl
inject₁-lemma (suc i) = cong suc (inject₁-lemma i)

inject≤-lemma : ∀ {m n} (i : Fin m) (le : m ℕ≤ n) →
                toℕ (inject≤ i le) ≡ toℕ i
inject≤-lemma zero    (N.s≤s le) = refl
inject≤-lemma (suc i) (N.s≤s le) = cong suc (inject≤-lemma i le)

-- Lemma:  inject≤ i n≤n ≡ i.
inject≤-refl : ∀ {n} (i : Fin n) (n≤n : n ℕ≤ n) → inject≤ i n≤n ≡ i
inject≤-refl zero    (s≤s _  ) = refl
inject≤-refl (suc i) (s≤s n≤n) = cong suc (inject≤-refl i n≤n)

≺⇒<′ : _≺_ ⇒ N._<′_
≺⇒<′ (n ≻toℕ i) = N.≤⇒≤′ (bounded i)

<′⇒≺ : N._<′_ ⇒ _≺_
<′⇒≺ {n} N.≤′-refl    = subst (λ i → i ≺ suc n) (to-from n)
                              (suc n ≻toℕ fromℕ n)
<′⇒≺ (N.≤′-step m≤′n) with <′⇒≺ m≤′n
<′⇒≺ (N.≤′-step m≤′n) | n ≻toℕ i =
  subst (λ i → i ≺ suc n) (inject₁-lemma i) (suc n ≻toℕ (inject₁ i))

toℕ-raise : ∀ {m} n (i : Fin m) → toℕ (raise n i) ≡ n ℕ+ toℕ i
toℕ-raise zero    i = refl
toℕ-raise (suc n) i = cong suc (toℕ-raise n i)

fromℕ≤-toℕ : ∀ {m} (i : Fin m) (i<m : toℕ i ℕ< m) → fromℕ≤ i<m ≡ i
fromℕ≤-toℕ zero    (s≤s z≤n)       = refl
fromℕ≤-toℕ (suc i) (s≤s (s≤s m≤n)) = cong suc (fromℕ≤-toℕ i (s≤s m≤n))

toℕ-fromℕ≤ : ∀ {m n} (m<n : m ℕ< n) → toℕ (fromℕ≤ m<n) ≡ m
toℕ-fromℕ≤ (s≤s z≤n)       = refl
toℕ-fromℕ≤ (s≤s (s≤s m<n)) = cong suc (toℕ-fromℕ≤ (s≤s m<n))

-- fromℕ is a special case of fromℕ≤.
fromℕ-def : ∀ n → fromℕ n ≡ fromℕ≤ ℕ≤-refl
fromℕ-def zero    = refl
fromℕ-def (suc n) = cong suc (fromℕ-def n)

-- fromℕ≤ and fromℕ≤″ give the same result.

fromℕ≤≡fromℕ≤″ :
  ∀ {m n} (m<n : m N.< n) (m<″n : m N.<″ n) →
  fromℕ≤ m<n ≡ fromℕ≤″ m m<″n
fromℕ≤≡fromℕ≤″ (s≤s z≤n)       (N.less-than-or-equal refl) = refl
fromℕ≤≡fromℕ≤″ (s≤s (s≤s m<n)) (N.less-than-or-equal refl) =
  cong suc (fromℕ≤≡fromℕ≤″ (s≤s m<n) (N.less-than-or-equal refl))

------------------------------------------------------------------------
-- Operations

infixl 6 _+′_

_+′_ : ∀ {m n} (i : Fin m) (j : Fin n) → Fin (N.pred m ℕ+ n)
i +′ j = inject≤ (i + j) (N._+-mono_ (prop-toℕ-≤ i) ℕ≤-refl)

-- reverse {n} "i" = "n ∸ 1 ∸ i".

reverse : ∀ {n} → Fin n → Fin n
reverse {zero}  ()
reverse {suc n} i  = inject≤ (n ℕ- i) (N.n∸m≤n (toℕ i) (suc n))

reverse-prop : ∀ {n} → (i : Fin n) → toℕ (reverse i) ≡ n ∸ suc (toℕ i)
reverse-prop {zero} ()
reverse-prop {suc n} i = begin
  toℕ (inject≤ (n ℕ- i) _)  ≡⟨ inject≤-lemma _ _ ⟩
  toℕ (n ℕ- i)              ≡⟨ toℕ‿ℕ- n i ⟩
  n ∸ toℕ i                 ∎
  where
  open P.≡-Reasoning

  toℕ‿ℕ- : ∀ n i → toℕ (n ℕ- i) ≡ n ∸ toℕ i
  toℕ‿ℕ- n       zero     = to-from n
  toℕ‿ℕ- zero    (suc ())
  toℕ‿ℕ- (suc n) (suc i)  = toℕ‿ℕ- n i

reverse-involutive : ∀ {n} → Involutive _≡_ reverse
reverse-involutive {n} i = toℕ-injective (begin
  toℕ (reverse (reverse i))  ≡⟨ reverse-prop _ ⟩
  n ∸ suc (toℕ (reverse i))  ≡⟨ eq ⟩
  toℕ i                      ∎)
  where
  open P.≡-Reasoning
  open CommutativeSemiring N.commutativeSemiring using (+-comm)

  lem₁ : ∀ m n → (m ℕ+ n) ∸ (m ℕ+ n ∸ m) ≡ m
  lem₁ m n = begin
    m ℕ+ n ∸ (m ℕ+ n ∸ m) ≡⟨ cong (λ ξ → m ℕ+ n ∸ (ξ ∸ m)) (+-comm m n) ⟩
    m ℕ+ n ∸ (n ℕ+ m ∸ m) ≡⟨ cong (λ ξ → m ℕ+ n ∸ ξ) (N.m+n∸n≡m n m) ⟩
    m ℕ+ n ∸ n            ≡⟨ N.m+n∸n≡m m n ⟩
    m                     ∎

  lem₂ : ∀ n → (i : Fin n) → n ∸ suc (n ∸ suc (toℕ i)) ≡ toℕ i
  lem₂ zero    ()
  lem₂ (suc n) i  = begin
    n ∸ (n ∸ toℕ i)                     ≡⟨ cong (λ ξ → ξ ∸ (ξ ∸ toℕ i)) i+j≡k ⟩
    (toℕ i ℕ+ j) ∸ (toℕ i ℕ+ j ∸ toℕ i) ≡⟨ lem₁ (toℕ i) j ⟩
    toℕ i                               ∎
    where
    decompose-n : ∃ λ j → n ≡ toℕ i ℕ+ j
    decompose-n = n ∸ toℕ i , P.sym (N.m+n∸m≡n (prop-toℕ-≤ i))

    j     = proj₁ decompose-n
    i+j≡k = proj₂ decompose-n

  eq : n ∸ suc (toℕ (reverse i)) ≡ toℕ i
  eq = begin
    n ∸ suc (toℕ (reverse i)) ≡⟨ cong (λ ξ → n ∸ suc ξ) (reverse-prop i) ⟩
    n ∸ suc (n ∸ suc (toℕ i)) ≡⟨ lem₂ n i ⟩
    toℕ i                     ∎

-- Lemma: reverse {suc n} (suc i) ≡ reverse n i  (in ℕ).

reverse-suc : ∀{n}{i : Fin n} → toℕ (reverse (suc i)) ≡ toℕ (reverse i)
reverse-suc {n}{i} = begin
  toℕ (reverse (suc i))      ≡⟨ reverse-prop (suc i) ⟩
  suc n ∸ suc (toℕ (suc i))  ≡⟨⟩
  n ∸ toℕ (suc i)            ≡⟨⟩
  n ∸ suc (toℕ i)            ≡⟨ P.sym (reverse-prop i) ⟩
  toℕ (reverse i)            ∎
  where
  open P.≡-Reasoning

-- If there is an injection from a type to a finite set, then the type
-- has decidable equality.

eq? : ∀ {a n} {A : Set a} → A ↣ Fin n → Decidable {A = A} _≡_
eq? inj = Dec.via-injection inj _≟_

-- Quantification over finite sets commutes with applicative functors.

sequence : ∀ {F n} {P : Fin n → Set} → RawApplicative F →
           (∀ i → F (P i)) → F (∀ i → P i)
sequence {F} RA = helper _ _
  where
  open RawApplicative RA

  helper : ∀ n (P : Fin n → Set) → (∀ i → F (P i)) → F (∀ i → P i)
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

  sequence⁻¹ : ∀ {F}{A} {P : A → Set} → RawFunctor F →
               F (∀ i → P i) → ∀ i → F (P i)
  sequence⁻¹ RF F∀iPi i = (λ f → f i) <$> F∀iPi
    where open RawFunctor RF
