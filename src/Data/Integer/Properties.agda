------------------------------------------------------------------------
-- The Agda standard library
--
-- Some properties about integers
------------------------------------------------------------------------

module Data.Integer.Properties where

open import Algebra
import Algebra.FunctionProperties
import Algebra.Morphism as Morphism
import Algebra.Properties.AbelianGroup
open import Algebra.Structures
open import Data.Integer hiding (_≤?_) renaming (suc to sucℤ)
open import Data.Nat
  using (ℕ; suc; zero; _∸_; _≤?_; s≤s; z≤n; ≤-pred)
  hiding (module ℕ)
  renaming (_+_ to _ℕ+_; _*_ to _ℕ*_;
    _<_ to _ℕ<_; _≥_ to _ℕ≥_; _≰_ to _ℕ≰_)
import Data.Nat.Properties as ℕₚ
open import Data.Product using (proj₁; proj₂; _,_)
open import Data.Sign as Sign using () renaming (_*_ to _𝕊*_)
import Data.Sign.Properties as 𝕊ₚ
open import Function using (_∘_; _$_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

open Algebra.FunctionProperties (_≡_ {A = ℤ})
open Morphism.Definitions ℤ ℕ _≡_
open ℕₚ.SemiringSolver
open ≡-Reasoning

------------------------------------------------------------------------
-- Equality

+-injective : ∀ {m n} → + m ≡ + n → m ≡ n
+-injective refl = refl

-[1+-injective : ∀ {m n} → -[1+ m ] ≡ -[1+ n ] → m ≡ n
-[1+-injective refl = refl

------------------------------------------------------------------------
-- Properties of -_

doubleNeg : ∀ n → - - n ≡ n
doubleNeg (+ zero)   = refl
doubleNeg (+ suc n)  = refl
doubleNeg (-[1+ n ]) = refl

neg-injective : ∀ {m n} → - m ≡ - n → m ≡ n
neg-injective {m} {n} -m≡-n = begin
  m     ≡⟨ sym (doubleNeg m) ⟩
  - - m ≡⟨ cong -_ -m≡-n ⟩
  - - n ≡⟨ doubleNeg n ⟩
  n ∎

------------------------------------------------------------------------
-- Properties of ∣_∣

∣n∣≡0⇒n≡0 : ∀ {n} → ∣ n ∣ ≡ 0 → n ≡ + 0
∣n∣≡0⇒n≡0 {+ .zero}   refl = refl
∣n∣≡0⇒n≡0 { -[1+ n ]} ()

∣-n∣≡∣n∣ : ∀ n → ∣ - n ∣ ≡ ∣ n ∣
∣-n∣≡∣n∣ (+ zero)   = refl
∣-n∣≡∣n∣ (+ suc n)  = refl
∣-n∣≡∣n∣ (-[1+ n ]) = refl

------------------------------------------------------------------------
-- Properties of sign and _◃_

+◃n≡+n : ∀ n → Sign.+ ◃ n ≡ + n
+◃n≡+n zero    = refl
+◃n≡+n (suc _) = refl

-◃n≡-n : ∀ n → Sign.- ◃ n ≡ - + n
-◃n≡-n zero    = refl
-◃n≡-n (suc _) = refl

sign-◃ : ∀ s n → sign (s ◃ suc n) ≡ s
sign-◃ Sign.- _ = refl
sign-◃ Sign.+ _ = refl

abs-◃ : ∀ s n → ∣ s ◃ n ∣ ≡ n
abs-◃ _      zero    = refl
abs-◃ Sign.- (suc n) = refl
abs-◃ Sign.+ (suc n) = refl

signₙ◃∣n∣≡n : ∀ n → sign n ◃ ∣ n ∣ ≡ n
signₙ◃∣n∣≡n (+ n)      = +◃n≡+n n
signₙ◃∣n∣≡n (-[1+ n ]) = refl

sign-cong : ∀ {s₁ s₂ n₁ n₂} →
            s₁ ◃ suc n₁ ≡ s₂ ◃ suc n₂ → s₁ ≡ s₂
sign-cong {s₁} {s₂} {n₁} {n₂} eq = begin
  s₁                  ≡⟨ sym $ sign-◃ s₁ n₁ ⟩
  sign (s₁ ◃ suc n₁)  ≡⟨ cong sign eq ⟩
  sign (s₂ ◃ suc n₂)  ≡⟨ sign-◃ s₂ n₂ ⟩
  s₂                  ∎

abs-cong : ∀ {s₁ s₂ n₁ n₂} →
           s₁ ◃ n₁ ≡ s₂ ◃ n₂ → n₁ ≡ n₂
abs-cong {s₁} {s₂} {n₁} {n₂} eq = begin
  n₁           ≡⟨ sym $ abs-◃ s₁ n₁ ⟩
  ∣ s₁ ◃ n₁ ∣  ≡⟨ cong ∣_∣ eq ⟩
  ∣ s₂ ◃ n₂ ∣  ≡⟨ abs-◃ s₂ n₂ ⟩
  n₂           ∎

∣s◃m∣*∣t◃n∣≡m*n : ∀ s t m n → ∣ s ◃ m ∣ ℕ* ∣ t ◃ n ∣ ≡ m ℕ* n
∣s◃m∣*∣t◃n∣≡m*n s t m n = cong₂ _ℕ*_ (abs-◃ s m) (abs-◃ t n)

------------------------------------------------------------------------
-- Properties of _⊖_

n⊖n≡0 : ∀ n → n ⊖ n ≡ + 0
n⊖n≡0 zero    = refl
n⊖n≡0 (suc n) = n⊖n≡0 n

⊖-swap : ∀ a b → a ⊖ b ≡ - (b ⊖ a)
⊖-swap zero    zero    = refl
⊖-swap (suc _) zero    = refl
⊖-swap zero    (suc _) = refl
⊖-swap (suc a) (suc b) = ⊖-swap a b

⊖-≥ : ∀ {m n} → m ℕ≥ n → m ⊖ n ≡ + (m ∸ n)
⊖-≥ z≤n       = refl
⊖-≥ (s≤s n≤m) = ⊖-≥ n≤m

⊖-< : ∀ {m n} → m ℕ< n → m ⊖ n ≡ - + (n ∸ m)
⊖-< {zero}  (s≤s z≤n) = refl
⊖-< {suc m} (s≤s m<n) = ⊖-< m<n

⊖-≰ : ∀ {m n} → n ℕ≰ m → m ⊖ n ≡ - + (n ∸ m)
⊖-≰ = ⊖-< ∘ ℕₚ.≰⇒>

∣⊖∣-< : ∀ {m n} → m ℕ< n → ∣ m ⊖ n ∣ ≡ n ∸ m
∣⊖∣-< {zero}  (s≤s z≤n) = refl
∣⊖∣-< {suc n} (s≤s m<n) = ∣⊖∣-< m<n

∣⊖∣-≰ : ∀ {m n} → n ℕ≰ m → ∣ m ⊖ n ∣ ≡ n ∸ m
∣⊖∣-≰ = ∣⊖∣-< ∘ ℕₚ.≰⇒>

sign-⊖-< : ∀ {m n} → m ℕ< n → sign (m ⊖ n) ≡ Sign.-
sign-⊖-< {zero}  (s≤s z≤n) = refl
sign-⊖-< {suc n} (s≤s m<n) = sign-⊖-< m<n

sign-⊖-≰ : ∀ {m n} → n ℕ≰ m → sign (m ⊖ n) ≡ Sign.-
sign-⊖-≰ = sign-⊖-< ∘ ℕₚ.≰⇒>

-[n⊖m]≡-m+n : ∀ m n → - (m ⊖ n) ≡ (- (+ m)) + (+ n)
-[n⊖m]≡-m+n zero    zero    = refl
-[n⊖m]≡-m+n zero    (suc n) = refl
-[n⊖m]≡-m+n (suc m) zero    = refl
-[n⊖m]≡-m+n (suc m) (suc n) = sym (⊖-swap n m)

+-⊖-left-cancel : ∀ a b c → (a ℕ+ b) ⊖ (a ℕ+ c) ≡ b ⊖ c
+-⊖-left-cancel zero    b c = refl
+-⊖-left-cancel (suc a) b c = +-⊖-left-cancel a b c

------------------------------------------------------------------------
-- Properties of _+_

+-comm : Commutative _+_
+-comm -[1+ a ] -[1+ b ] rewrite ℕₚ.+-comm a b = refl
+-comm (+   a ) (+   b ) rewrite ℕₚ.+-comm a b = refl
+-comm -[1+ _ ] (+   _ ) = refl
+-comm (+   _ ) -[1+ _ ] = refl

+-identityˡ : LeftIdentity (+ 0) _+_
+-identityˡ -[1+ _ ] = refl
+-identityˡ (+   _ ) = refl

+-identityʳ : RightIdentity (+ 0) _+_
+-identityʳ x rewrite +-comm x (+ 0) = +-identityˡ x

+-identity : Identity (+ 0) _+_
+-identity = +-identityˡ , +-identityʳ

distribˡ-⊖-+-neg : ∀ a b c → b ⊖ c + -[1+ a ] ≡ b ⊖ (suc c ℕ+ a)
distribˡ-⊖-+-neg _ zero    zero    = refl
distribˡ-⊖-+-neg _ zero    (suc _) = refl
distribˡ-⊖-+-neg _ (suc _) zero    = refl
distribˡ-⊖-+-neg a (suc b) (suc c) = distribˡ-⊖-+-neg a b c

distribʳ-⊖-+-neg : ∀ a b c → -[1+ a ] + (b ⊖ c) ≡ b ⊖ (suc a ℕ+ c)
distribʳ-⊖-+-neg a b c
  rewrite +-comm -[1+ a ] (b ⊖ c)
        | distribˡ-⊖-+-neg a b c
        | ℕₚ.+-comm a c
        = refl

distribˡ-⊖-+-pos : ∀ a b c → b ⊖ c + + a ≡ b ℕ+ a ⊖ c
distribˡ-⊖-+-pos _ zero    zero    = refl
distribˡ-⊖-+-pos _ zero    (suc _) = refl
distribˡ-⊖-+-pos _ (suc _) zero    = refl
distribˡ-⊖-+-pos a (suc b) (suc c) = distribˡ-⊖-+-pos a b c

distribʳ-⊖-+-pos : ∀ a b c → + a + (b ⊖ c) ≡ a ℕ+ b ⊖ c
distribʳ-⊖-+-pos a b c
  rewrite +-comm (+ a) (b ⊖ c)
        | distribˡ-⊖-+-pos a b c
        | ℕₚ.+-comm a b
        = refl

+-assoc : Associative _+_
+-assoc (+ zero) y z rewrite +-identityˡ      y  | +-identityˡ (y + z) = refl
+-assoc x (+ zero) z rewrite +-identityʳ  x      | +-identityˡ      z  = refl
+-assoc x y (+ zero) rewrite +-identityʳ (x + y) | +-identityʳ  y      = refl
+-assoc -[1+ a ]  -[1+ b ]  (+ suc c) = sym (distribʳ-⊖-+-neg a c b)
+-assoc -[1+ a ]  (+ suc b) (+ suc c) = distribˡ-⊖-+-pos (suc c) b a
+-assoc (+ suc a) -[1+ b ]  -[1+ c ]  = distribˡ-⊖-+-neg c a b
+-assoc (+ suc a) -[1+ b ] (+ suc c)
  rewrite distribˡ-⊖-+-pos (suc c) a b
        | distribʳ-⊖-+-pos (suc a) c b
        | sym (ℕₚ.+-assoc a 1 c)
        | ℕₚ.+-comm a 1
        = refl
+-assoc (+ suc a) (+ suc b) -[1+ c ]
  rewrite distribʳ-⊖-+-pos (suc a) b c
        | sym (ℕₚ.+-assoc a 1 b)
        | ℕₚ.+-comm a 1
        = refl
+-assoc -[1+ a ] -[1+ b ] -[1+ c ]
  rewrite sym (ℕₚ.+-assoc a 1 (b ℕ+ c))
        | ℕₚ.+-comm a 1
        | ℕₚ.+-assoc a b c
        = refl
+-assoc -[1+ a ] (+ suc b) -[1+ c ]
  rewrite distribʳ-⊖-+-neg a b c
        | distribˡ-⊖-+-neg c b a
        = refl
+-assoc (+ suc a) (+ suc b) (+ suc c)
  rewrite ℕₚ.+-assoc (suc a) (suc b) (suc c)
        = refl

inverseˡ : LeftInverse (+ 0) -_ _+_
inverseˡ -[1+ n ]  = n⊖n≡0 n
inverseˡ (+ zero)  = refl
inverseˡ (+ suc n) = n⊖n≡0 n

inverseʳ : RightInverse (+ 0) -_ _+_
inverseʳ i = begin
  i + - i  ≡⟨ +-comm i (- i) ⟩
  - i + i  ≡⟨ inverseˡ i ⟩
  + 0      ∎

+-inverse : Inverse (+ 0) -_ _+_
+-inverse = inverseˡ , inverseʳ

+-isSemigroup : IsSemigroup _≡_ _+_
+-isSemigroup = record
  { isEquivalence = isEquivalence
  ; assoc         = +-assoc
  ; ∙-cong        = cong₂ _+_
  }

+-0-isMonoid : IsMonoid _≡_ _+_ (+ 0)
+-0-isMonoid = record
  { isSemigroup = +-isSemigroup
  ; identity    = +-identity
  }

+-0-isCommutativeMonoid : IsCommutativeMonoid _≡_ _+_ (+ 0)
+-0-isCommutativeMonoid = record
  { isSemigroup = +-isSemigroup
  ; identityˡ   = +-identityˡ
  ; comm        = +-comm
  }

+-0-commutativeMonoid : CommutativeMonoid _ _
+-0-commutativeMonoid = record
  { Carrier             = ℤ
  ; _≈_                 = _≡_
  ; _∙_                 = _+_
  ; ε                   = + 0
  ; isCommutativeMonoid = +-0-isCommutativeMonoid
  }

+-0-isGroup : IsGroup _≡_ _+_ (+ 0) (-_)
+-0-isGroup = record
  { isMonoid = +-0-isMonoid
  ; inverse  = +-inverse
  ; ⁻¹-cong  = cong (-_)
  }

+-isAbelianGroup : IsAbelianGroup _≡_ _+_ (+ 0) (-_)
+-isAbelianGroup = record
  { isGroup = +-0-isGroup
  ; comm    = +-comm
  }

+-0-abelianGroup : AbelianGroup _ _
+-0-abelianGroup = record
  { Carrier = ℤ
  ; _≈_ = _≡_
  ; _∙_ = _+_
  ; ε = + 0
  ; _⁻¹ = -_
  ; isAbelianGroup = +-isAbelianGroup
  }

open Algebra.Properties.AbelianGroup +-0-abelianGroup
  using () renaming (⁻¹-involutive to -‿involutive)

-- Other properties of _+_

neg-distrib-+ : ∀ m n → - (m + n) ≡ (- m) + (- n)
neg-distrib-+ (+ zero)  (+ zero)  = refl
neg-distrib-+ (+ zero)  (+ suc n) = refl
neg-distrib-+ (+ suc m) (+ zero)  = cong -[1+_] (ℕₚ.+-right-identity m)
neg-distrib-+ (+ suc m) (+ suc n) = cong -[1+_] (ℕₚ.+-suc m n)
neg-distrib-+ -[1+ m ]  -[1+ n ] = cong (λ v → + suc v) (sym (ℕₚ.+-suc m n))
neg-distrib-+ (+   m)   -[1+ n ] = -[n⊖m]≡-m+n m (suc n)
neg-distrib-+ -[1+ m ]  (+   n)  =
  trans (-[n⊖m]≡-m+n n (suc m)) (+-comm (- + n) (+ suc m))

◃-distrib-+ : ∀ s m n → s ◃ (m ℕ+ n) ≡ (s ◃ m) + (s ◃ n)
◃-distrib-+ Sign.- m n = begin
  Sign.- ◃ (m ℕ+ n)           ≡⟨ -◃n≡-n (m ℕ+ n) ⟩
  - (+ (m ℕ+ n))              ≡⟨⟩
  - ((+ m) + (+ n))           ≡⟨ neg-distrib-+ (+ m) (+ n) ⟩
  (- (+ m)) + (- (+ n))       ≡⟨ sym (cong₂ _+_ (-◃n≡-n m) (-◃n≡-n n)) ⟩
  (Sign.- ◃ m) + (Sign.- ◃ n) ∎
◃-distrib-+ Sign.+ m n = begin
  Sign.+ ◃ (m ℕ+ n)           ≡⟨ +◃n≡+n (m ℕ+ n) ⟩
  + (m ℕ+ n)                  ≡⟨⟩
  (+ m) + (+ n)               ≡⟨ sym (cong₂ _+_ (+◃n≡+n m) (+◃n≡+n n)) ⟩
  (Sign.+ ◃ m) + (Sign.+ ◃ n) ∎


------------------------------------------------------------------------
-- Properties of _*_

*-comm : Commutative _*_
*-comm -[1+ a ] -[1+ b ] rewrite ℕₚ.*-comm (suc a) (suc b) = refl
*-comm -[1+ a ] (+   b ) rewrite ℕₚ.*-comm (suc a) b       = refl
*-comm (+   a ) -[1+ b ] rewrite ℕₚ.*-comm a       (suc b) = refl
*-comm (+   a ) (+   b ) rewrite ℕₚ.*-comm a       b       = refl

*-identityˡ : LeftIdentity (+ 1) _*_
*-identityˡ (+ zero ) = refl
*-identityˡ -[1+  n ] rewrite ℕₚ.+-right-identity n = refl
*-identityˡ (+ suc n) rewrite ℕₚ.+-right-identity n = refl

*-identityʳ : RightIdentity (+ 1) _*_
*-identityʳ x rewrite
    𝕊ₚ.*-identityʳ (sign x)
  | ℕₚ.*-right-identity ∣ x ∣
  | signₙ◃∣n∣≡n x
  = refl

*-identity : Identity (+ 1) _*_
*-identity = *-identityˡ , *-identityʳ

*-zeroˡ : LeftZero (+ 0) _*_
*-zeroˡ n = refl

*-zeroʳ : RightZero (+ 0) _*_
*-zeroʳ n rewrite *-comm n (+ 0) = refl

*-zero : Zero (+ 0) _*_
*-zero = *-zeroˡ , *-zeroʳ

private
  lemma : ∀ a b c → c ℕ+ (b ℕ+ a ℕ* suc b) ℕ* suc c
                  ≡ c ℕ+ b ℕ* suc c ℕ+ a ℕ* suc (c ℕ+ b ℕ* suc c)
  lemma =
    solve 3 (λ a b c → c :+ (b :+ a :* (con 1 :+ b)) :* (con 1 :+ c)
                    := c :+ b :* (con 1 :+ c) :+
                       a :* (con 1 :+ (c :+ b :* (con 1 :+ c))))
            refl
    where open ℕₚ.SemiringSolver

*-assoc : Associative _*_
*-assoc (+ zero) _ _ = refl
*-assoc x (+ zero) _ rewrite ℕₚ.*-right-zero ∣ x ∣ = refl
*-assoc x y (+ zero) rewrite
    ℕₚ.*-right-zero ∣ y ∣
  | ℕₚ.*-right-zero ∣ x ∣
  | ℕₚ.*-right-zero ∣ sign x 𝕊* sign y ◃ ∣ x ∣ ℕ* ∣ y ∣ ∣
  = refl
*-assoc -[1+ a  ] -[1+ b  ] (+ suc c) = cong (+_ ∘ suc) (lemma a b c)
*-assoc -[1+ a  ] (+ suc b) -[1+ c  ] = cong (+_ ∘ suc) (lemma a b c)
*-assoc (+ suc a) (+ suc b) (+ suc c) = cong (+_ ∘ suc) (lemma a b c)
*-assoc (+ suc a) -[1+ b  ] -[1+ c  ] = cong (+_ ∘ suc) (lemma a b c)
*-assoc -[1+ a  ] -[1+ b  ] -[1+ c  ] = cong -[1+_]     (lemma a b c)
*-assoc -[1+ a  ] (+ suc b) (+ suc c) = cong -[1+_]     (lemma a b c)
*-assoc (+ suc a) -[1+ b  ] (+ suc c) = cong -[1+_]     (lemma a b c)
*-assoc (+ suc a) (+ suc b) -[1+ c  ] = cong -[1+_]     (lemma a b c)

*-isSemigroup : IsSemigroup _ _
*-isSemigroup = record
  { isEquivalence = isEquivalence
  ; assoc         = *-assoc
  ; ∙-cong        = cong₂ _*_
  }

*-1-isMonoid : IsMonoid _≡_ _*_ (+ 1)
*-1-isMonoid = record
  { isSemigroup = *-isSemigroup
  ; identity    = *-identity
  }

*-1-isCommutativeMonoid : IsCommutativeMonoid _≡_ _*_ (+ 1)
*-1-isCommutativeMonoid = record
  { isSemigroup = *-isSemigroup
  ; identityˡ   = *-identityˡ
  ; comm        = *-comm
  }

*-1-commutativeMonoid : CommutativeMonoid _ _
*-1-commutativeMonoid = record
  { Carrier             = ℤ
  ; _≈_                 = _≡_
  ; _∙_                 = _*_
  ; ε                   = + 1
  ; isCommutativeMonoid = *-1-isCommutativeMonoid
  }

------------------------------------------------------------------------
-- The integers form a commutative ring

-- Distributivity

private

  -- lemma used to prove distributivity.

  distrib-lemma :
    ∀ a b c → (c ⊖ b) * -[1+ a ] ≡ a ℕ+ b ℕ* suc a ⊖ (a ℕ+ c ℕ* suc a)
  distrib-lemma a b c
    rewrite +-⊖-left-cancel a (b ℕ* suc a) (c ℕ* suc a)
          | ⊖-swap (b ℕ* suc a) (c ℕ* suc a)
    with b ≤? c
  ... | yes b≤c
    rewrite ⊖-≥ b≤c
          | ⊖-≥ (ℕₚ.*-mono-≤ b≤c (ℕₚ.≤-refl {x = suc a}))
          | -◃n≡-n ((c ∸ b) ℕ* suc a)
          | ℕₚ.*-distrib-∸ʳ (suc a) c b
          = refl
  ... | no b≰c
    rewrite sign-⊖-≰ b≰c
          | ∣⊖∣-≰ b≰c
          | +◃n≡+n ((b ∸ c) ℕ* suc a)
          | ⊖-≰ (b≰c ∘ ℕₚ.cancel-*-right-≤ b c a)
          | -‿involutive (+ (b ℕ* suc a ∸ c ℕ* suc a))
          | ℕₚ.*-distrib-∸ʳ (suc a) b c
          = refl

distribʳ : _*_ DistributesOverʳ _+_

distribʳ (+ zero) y z
  rewrite ℕₚ.*-right-zero ∣ y ∣
        | ℕₚ.*-right-zero ∣ z ∣
        | ℕₚ.*-right-zero ∣ y + z ∣
        = refl

distribʳ x (+ zero) z
  rewrite +-identityˡ z
        | +-identityˡ (sign z 𝕊* sign x ◃ ∣ z ∣ ℕ* ∣ x ∣)
        = refl

distribʳ x y (+ zero)
  rewrite +-identityʳ y
        | +-identityʳ (sign y 𝕊* sign x ◃ ∣ y ∣ ℕ* ∣ x ∣)
        = refl

distribʳ -[1+ a ] -[1+ b ] -[1+ c ] = cong (+_) $
  solve 3 (λ a b c → (con 2 :+ b :+ c) :* (con 1 :+ a)
                  := (con 1 :+ b) :* (con 1 :+ a) :+
                     (con 1 :+ c) :* (con 1 :+ a))
          refl a b c

distribʳ (+ suc a) (+ suc b) (+ suc c) = cong (+_) $
  solve 3 (λ a b c → (con 1 :+ b :+ (con 1 :+ c)) :* (con 1 :+ a)
                  := (con 1 :+ b) :* (con 1 :+ a) :+
                     (con 1 :+ c) :* (con 1 :+ a))
        refl a b c

distribʳ -[1+ a ] (+ suc b) (+ suc c) = cong -[1+_] $
  solve 3 (λ a b c → a :+ (b :+ (con 1 :+ c)) :* (con 1 :+ a)
                   := (con 1 :+ b) :* (con 1 :+ a) :+
                      (a :+ c :* (con 1 :+ a)))
         refl a b c

distribʳ (+ suc a) -[1+ b ] -[1+ c ] = cong -[1+_] $
  solve 3 (λ a b c → a :+ (con 1 :+ a :+ (b :+ c) :* (con 1 :+ a))
                  := (con 1 :+ b) :* (con 1 :+ a) :+
                     (a :+ c :* (con 1 :+ a)))
         refl a b c

distribʳ -[1+ a ] -[1+ b ] (+ suc c) = distrib-lemma a b c

distribʳ -[1+ a ] (+ suc b) -[1+ c ] = distrib-lemma a c b

distribʳ (+ suc a) -[1+ b ] (+ suc c)
  rewrite +-⊖-left-cancel a (c ℕ* suc a) (b ℕ* suc a)
  with b ≤? c
... | yes b≤c
  rewrite ⊖-≥ b≤c
        | +-comm (- (+ (a ℕ+ b ℕ* suc a))) (+ (a ℕ+ c ℕ* suc a))
        | ⊖-≥ (ℕₚ.*-mono-≤ b≤c (ℕₚ.≤-refl {x = suc a}))
        | ℕₚ.*-distrib-∸ʳ (suc a) c b
        | +◃n≡+n (c ℕ* suc a ∸ b ℕ* suc a)
        = refl
... | no b≰c
  rewrite sign-⊖-≰ b≰c
        | ∣⊖∣-≰ b≰c
        | -◃n≡-n ((b ∸ c) ℕ* suc a)
        | ⊖-≰ (b≰c ∘ ℕₚ.cancel-*-right-≤ b c a)
        | ℕₚ.*-distrib-∸ʳ (suc a) b c
        = refl

distribʳ (+ suc c) (+ suc a) -[1+ b ]
  rewrite +-⊖-left-cancel c (a ℕ* suc c) (b ℕ* suc c)
  with b ≤? a
... | yes b≤a
  rewrite ⊖-≥ b≤a
        | ⊖-≥ (ℕₚ.*-mono-≤ b≤a (ℕₚ.≤-refl {x = suc c}))
        | +◃n≡+n ((a ∸ b) ℕ* suc c)
        | ℕₚ.*-distrib-∸ʳ (suc c) a b
        = refl
... | no b≰a
  rewrite sign-⊖-≰ b≰a
        | ∣⊖∣-≰ b≰a
        | ⊖-≰ (b≰a ∘ ℕₚ.cancel-*-right-≤ b a c)
        | -◃n≡-n ((b ∸ a) ℕ* suc c)
        | ℕₚ.*-distrib-∸ʳ (suc c) b a
        = refl

isCommutativeSemiring : IsCommutativeSemiring _≡_ _+_ _*_ (+ 0) (+ 1)
isCommutativeSemiring = record
  { +-isCommutativeMonoid = +-0-isCommutativeMonoid
  ; *-isCommutativeMonoid = *-1-isCommutativeMonoid
  ; distribʳ              = distribʳ
  ; zeroˡ                 = λ _ → refl
  }

+-*-isRing : IsRing _≡_ _+_ _*_ -_ (+ 0) (+ 1)
+-*-isRing = record
  { +-isAbelianGroup = +-isAbelianGroup
  ; *-isMonoid       = *-1-isMonoid
  ; distrib          = IsCommutativeSemiring.distrib
                         isCommutativeSemiring
  }

+-*-isCommutativeRing : IsCommutativeRing _≡_ _+_ _*_ -_ (+ 0) (+ 1)
+-*-isCommutativeRing = record
  { isRing = +-*-isRing
  ; *-comm = *-comm
  }

commutativeRing : CommutativeRing _ _
commutativeRing = record
  { Carrier           = ℤ
  ; _≈_               = _≡_
  ; _+_               = _+_
  ; _*_               = _*_
  ; -_                = -_
  ; 0#                = + 0
  ; 1#                = + 1
  ; isCommutativeRing = +-*-isCommutativeRing
  }

import Algebra.RingSolver.Simple as Solver
import Algebra.RingSolver.AlmostCommutativeRing as ACR
module RingSolver =
  Solver (ACR.fromCommutativeRing commutativeRing) _≟_

-- Other properties of _*_

abs-*-commute : Homomorphic₂ ∣_∣ _*_ _ℕ*_
abs-*-commute i j = abs-◃ _ _

cancel-*-right : ∀ i j k → k ≢ + 0 → i * k ≡ j * k → i ≡ j
cancel-*-right i j k            ≢0 eq with signAbs k
cancel-*-right i j .(+ 0)       ≢0 eq | s ◂ zero  = contradiction refl ≢0
cancel-*-right i j .(s ◃ suc n) ≢0 eq | s ◂ suc n
  with ∣ s ◃ suc n ∣ | abs-◃ s (suc n) | sign (s ◃ suc n) | sign-◃ s n
...  | .(suc n)      | refl            | .s               | refl =
  ◃-cong (sign-i≡sign-j i j eq) $
         ℕₚ.cancel-*-right ∣ i ∣ ∣ j ∣ $ abs-cong eq
  where
  sign-i≡sign-j : ∀ i j →
                  sign i 𝕊* s ◃ ∣ i ∣ ℕ* suc n ≡
                  sign j 𝕊* s ◃ ∣ j ∣ ℕ* suc n →
                  sign i ≡ sign j
  sign-i≡sign-j i              j              eq with signAbs i | signAbs j
  sign-i≡sign-j .(+ 0)         .(+ 0)         eq | s₁ ◂ zero   | s₂ ◂ zero   = refl
  sign-i≡sign-j .(+ 0)         .(s₂ ◃ suc n₂) eq | s₁ ◂ zero   | s₂ ◂ suc n₂
    with ∣ s₂ ◃ suc n₂ ∣ | abs-◃ s₂ (suc n₂)
  ... | .(suc n₂) | refl
    with abs-cong {s₁} {sign (s₂ ◃ suc n₂) 𝕊* s} {0} {suc n₂ ℕ* suc n} eq
  ...   | ()
  sign-i≡sign-j .(s₁ ◃ suc n₁) .(+ 0)         eq | s₁ ◂ suc n₁ | s₂ ◂ zero
    with ∣ s₁ ◃ suc n₁ ∣ | abs-◃ s₁ (suc n₁)
  ... | .(suc n₁) | refl
    with abs-cong {sign (s₁ ◃ suc n₁) 𝕊* s} {s₁} {suc n₁ ℕ* suc n} {0} eq
  ...   | ()
  sign-i≡sign-j .(s₁ ◃ suc n₁) .(s₂ ◃ suc n₂) eq | s₁ ◂ suc n₁ | s₂ ◂ suc n₂
    with ∣ s₁ ◃ suc n₁ ∣ | abs-◃ s₁ (suc n₁)
       | sign (s₁ ◃ suc n₁) | sign-◃ s₁ n₁
       | ∣ s₂ ◃ suc n₂ ∣ | abs-◃ s₂ (suc n₂)
       | sign (s₂ ◃ suc n₂) | sign-◃ s₂ n₂
  ... | .(suc n₁) | refl | .s₁ | refl | .(suc n₂) | refl | .s₂ | refl =
    𝕊ₚ.cancel-*-right s₁ s₂ (sign-cong eq)

cancel-*-+-right-≤ : ∀ m n o → m * + suc o ≤ n * + suc o → m ≤ n
cancel-*-+-right-≤ (-[1+ m ]) (-[1+ n ]) o (-≤- n≤m) =
  -≤- (≤-pred (ℕₚ.cancel-*-right-≤ (suc n) (suc m) o (s≤s n≤m)))
cancel-*-+-right-≤ -[1+ _ ]   (+ _)      _ _         = -≤+
cancel-*-+-right-≤ (+ 0)      -[1+ _ ]   _ ()
cancel-*-+-right-≤ (+ suc _)  -[1+ _ ]   _ ()
cancel-*-+-right-≤ (+ 0)      (+ 0)      _ _         = +≤+ z≤n
cancel-*-+-right-≤ (+ 0)      (+ suc _)  _ _         = +≤+ z≤n
cancel-*-+-right-≤ (+ suc _)  (+ 0)      _ (+≤+ ())
cancel-*-+-right-≤ (+ suc m)  (+ suc n)  o (+≤+ m≤n) =
  +≤+ (ℕₚ.cancel-*-right-≤ (suc m) (suc n) o m≤n)

*-+-right-mono : ∀ n → (λ x → x * + suc n) Preserves _≤_ ⟶ _≤_
*-+-right-mono _ (-≤+             {n = 0})         = -≤+
*-+-right-mono _ (-≤+             {n = suc _})     = -≤+
*-+-right-mono x (-≤-                         n≤m) =
  -≤- (≤-pred (ℕₚ.*-mono-≤ (s≤s n≤m) (ℕₚ.≤-refl {x = suc x})))
*-+-right-mono _ (+≤+ {m = 0}     {n = 0}     m≤n) = +≤+ m≤n
*-+-right-mono _ (+≤+ {m = 0}     {n = suc _} m≤n) = +≤+ z≤n
*-+-right-mono _ (+≤+ {m = suc _} {n = 0}     ())
*-+-right-mono x (+≤+ {m = suc _} {n = suc _} m≤n) =
  +≤+ ((ℕₚ.*-mono-≤ m≤n (ℕₚ.≤-refl {x = suc x})))

-1*n≡-n : ∀ n → -[1+ 0 ] * n ≡ - n
-1*n≡-n (+ zero)  = refl
-1*n≡-n (+ suc n) = cong -[1+_] (ℕₚ.+-right-identity n)
-1*n≡-n -[1+ n ]  = cong (λ v → + suc v) (ℕₚ.+-right-identity n)

◃-distrib-* :  ∀ s t m n → (s 𝕊* t) ◃ (m ℕ* n) ≡ (s ◃ m) * (t ◃ n)
◃-distrib-* s t zero zero    = refl
◃-distrib-* s t zero (suc n) = refl
◃-distrib-* s t (suc m) zero =
  trans
    (cong₂ _◃_ (𝕊ₚ.*-comm s t) (ℕₚ.*-comm m 0))
    (*-comm (t ◃ zero) (s ◃ suc m))
◃-distrib-* s t (suc m) (suc n) =
  sym (cong₂ _◃_
    (cong₂ _𝕊*_ (sign-◃ s m) (sign-◃ t n))
    (∣s◃m∣*∣t◃n∣≡m*n s t (suc m) (suc n)))
