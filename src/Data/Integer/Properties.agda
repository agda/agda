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
open import Data.Integer hiding (suc; _≤?_)
import Data.Integer.Addition.Properties as Add
import Data.Integer.Multiplication.Properties as Mul
open import Data.Nat
  using (ℕ; suc; zero; _∸_; _≤?_; _<_; _≥_; _≱_; s≤s; z≤n; ≤-pred)
  hiding (module ℕ)
  renaming (_+_ to _ℕ+_; _*_ to _ℕ*_)
open import Data.Nat.Properties as ℕ using (_*-mono_; ≤-refl)
open import Data.Product using (proj₁; proj₂; _,_)
open import Data.Sign as Sign using () renaming (_*_ to _S*_)
import Data.Sign.Properties as SignProp
open import Function using (_∘_; _$_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

open Algebra.FunctionProperties (_≡_ {A = ℤ})
open CommutativeMonoid Add.commutativeMonoid
  using ()
  renaming ( assoc to +-assoc; comm to +-comm; identity to +-identity
           ; isCommutativeMonoid to +-isCommutativeMonoid
           ; isMonoid to +-isMonoid
           )
open CommutativeMonoid Mul.commutativeMonoid
  using ()
  renaming ( assoc to *-assoc; comm to *-comm; identity to *-identity
           ; isCommutativeMonoid to *-isCommutativeMonoid
           ; isMonoid to *-isMonoid
           )
open CommutativeSemiring ℕ.commutativeSemiring
  using () renaming (zero to *-zero; distrib to *-distrib)
open Morphism.Definitions ℤ ℕ _≡_
open ℕ.SemiringSolver
open ≡-Reasoning

------------------------------------------------------------------------
-- Miscellaneous properties

-- Some properties relating sign and ∣_∣ to _◃_.

sign-◃ : ∀ s n → sign (s ◃ suc n) ≡ s
sign-◃ Sign.- _ = refl
sign-◃ Sign.+ _ = refl

sign-cong : ∀ {s₁ s₂ n₁ n₂} →
            s₁ ◃ suc n₁ ≡ s₂ ◃ suc n₂ → s₁ ≡ s₂
sign-cong {s₁} {s₂} {n₁} {n₂} eq = begin
  s₁                  ≡⟨ sym $ sign-◃ s₁ n₁ ⟩
  sign (s₁ ◃ suc n₁)  ≡⟨ cong sign eq ⟩
  sign (s₂ ◃ suc n₂)  ≡⟨ sign-◃ s₂ n₂ ⟩
  s₂                  ∎

abs-◃ : ∀ s n → ∣ s ◃ n ∣ ≡ n
abs-◃ _      zero    = refl
abs-◃ Sign.- (suc n) = refl
abs-◃ Sign.+ (suc n) = refl

abs-cong : ∀ {s₁ s₂ n₁ n₂} →
           s₁ ◃ n₁ ≡ s₂ ◃ n₂ → n₁ ≡ n₂
abs-cong {s₁} {s₂} {n₁} {n₂} eq = begin
  n₁           ≡⟨ sym $ abs-◃ s₁ n₁ ⟩
  ∣ s₁ ◃ n₁ ∣  ≡⟨ cong ∣_∣ eq ⟩
  ∣ s₂ ◃ n₂ ∣  ≡⟨ abs-◃ s₂ n₂ ⟩
  n₂           ∎

-- ∣_∣ commutes with multiplication.

abs-*-commute : Homomorphic₂ ∣_∣ _*_ _ℕ*_
abs-*-commute i j = abs-◃ _ _

-- Subtraction properties

n⊖n≡0 : ∀ n → n ⊖ n ≡ + 0
n⊖n≡0 zero    = refl
n⊖n≡0 (suc n) = n⊖n≡0 n

sign-⊖-< : ∀ {m n} → m < n → sign (m ⊖ n) ≡ Sign.-
sign-⊖-< {zero}  (s≤s z≤n) = refl
sign-⊖-< {suc n} (s≤s m<n) = sign-⊖-< m<n

+-⊖-left-cancel : ∀ a b c → (a ℕ+ b) ⊖ (a ℕ+ c) ≡ b ⊖ c
+-⊖-left-cancel zero    b c = refl
+-⊖-left-cancel (suc a) b c = +-⊖-left-cancel a b c

⊖-swap : ∀ a b → a ⊖ b ≡ - (b ⊖ a)
⊖-swap zero    zero    = refl
⊖-swap (suc _) zero    = refl
⊖-swap zero    (suc _) = refl
⊖-swap (suc a) (suc b) = ⊖-swap a b

⊖-≥ : ∀ {m n} → m ≥ n → m ⊖ n ≡ + (m ∸ n)
⊖-≥ z≤n       = refl
⊖-≥ (s≤s n≤m) = ⊖-≥ n≤m

⊖-< : ∀ {m n} → m < n → m ⊖ n ≡ - + (n ∸ m)
⊖-< {zero}  (s≤s z≤n) = refl
⊖-< {suc m} (s≤s m<n) = ⊖-< m<n

∣⊖∣-< : ∀ {m n} → m < n → ∣ m ⊖ n ∣ ≡ n ∸ m
∣⊖∣-< {zero}  (s≤s z≤n) = refl
∣⊖∣-< {suc n} (s≤s m<n) = ∣⊖∣-< m<n


------------------------------------------------------------------------
-- The integers form a commutative ring

-- Additive abelian group.

inverseˡ : LeftInverse (+ 0) -_ _+_
inverseˡ -[1+ n ]  = n⊖n≡0 n
inverseˡ (+ zero)  = refl
inverseˡ (+ suc n) = n⊖n≡0 n

inverseʳ : RightInverse (+ 0) -_ _+_
inverseʳ i = begin
  i + - i  ≡⟨ +-comm i (- i) ⟩
  - i + i  ≡⟨ inverseˡ i ⟩
  + 0      ∎

+-isAbelianGroup : IsAbelianGroup _≡_ _+_ (+ 0) (-_)
+-isAbelianGroup = record
  { isGroup = record
    { isMonoid = +-isMonoid
    ; inverse  = inverseˡ , inverseʳ
    ; ⁻¹-cong  = cong (-_)
    }
  ; comm = +-comm
  }

open Algebra.Properties.AbelianGroup
       (record { isAbelianGroup = +-isAbelianGroup })
  using () renaming (⁻¹-involutive to -‿involutive)


-- Distributivity

private

  -- Various lemmas used to prove distributivity.

  sign-⊖-≱ : ∀ {m n} → m ≱ n → sign (m ⊖ n) ≡ Sign.-
  sign-⊖-≱ = sign-⊖-< ∘ ℕ.≰⇒>

  ∣⊖∣-≱ : ∀ {m n} → m ≱ n → ∣ m ⊖ n ∣ ≡ n ∸ m
  ∣⊖∣-≱ = ∣⊖∣-< ∘ ℕ.≰⇒>

  ⊖-≱ : ∀ {m n} → m ≱ n → m ⊖ n ≡ - + (n ∸ m)
  ⊖-≱ = ⊖-< ∘ ℕ.≰⇒>

  -- Lemmas working around the fact that _◃_ pattern matches on its
  -- second argument before its first.

  +‿◃ : ∀ n → Sign.+ ◃ n ≡ + n
  +‿◃ zero    = refl
  +‿◃ (suc _) = refl

  -‿◃ : ∀ n → Sign.- ◃ n ≡ - + n
  -‿◃ zero    = refl
  -‿◃ (suc _) = refl

  distrib-lemma :
    ∀ a b c → (c ⊖ b) * -[1+ a ] ≡ a ℕ+ b ℕ* suc a ⊖ (a ℕ+ c ℕ* suc a)
  distrib-lemma a b c
    rewrite +-⊖-left-cancel a (b ℕ* suc a) (c ℕ* suc a)
          | ⊖-swap (b ℕ* suc a) (c ℕ* suc a)
    with b ≤? c
  ... | yes b≤c
    rewrite ⊖-≥ b≤c
          | ⊖-≥ (b≤c *-mono (≤-refl {x = suc a}))
          | -‿◃ ((c ∸ b) ℕ* suc a)
          | ℕ.*-distrib-∸ʳ (suc a) c b
          = refl
  ... | no b≰c
    rewrite sign-⊖-≱ b≰c
          | ∣⊖∣-≱ b≰c
          | +‿◃ ((b ∸ c) ℕ* suc a)
          | ⊖-≱ (b≰c ∘ ℕ.cancel-*-right-≤ b c a)
          | -‿involutive (+ (b ℕ* suc a ∸ c ℕ* suc a))
          | ℕ.*-distrib-∸ʳ (suc a) b c
          = refl

distribʳ : _*_ DistributesOverʳ _+_

distribʳ (+ zero) y z
  rewrite proj₂ *-zero ∣ y ∣
        | proj₂ *-zero ∣ z ∣
        | proj₂ *-zero ∣ y + z ∣
        = refl

distribʳ x (+ zero) z
  rewrite proj₁ +-identity z
        | proj₁ +-identity (sign z S* sign x ◃ ∣ z ∣ ℕ* ∣ x ∣)
        = refl

distribʳ x y (+ zero)
  rewrite proj₂ +-identity y
        | proj₂ +-identity (sign y S* sign x ◃ ∣ y ∣ ℕ* ∣ x ∣)
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
        | ⊖-≥ (b≤c *-mono ≤-refl {x = suc a})
        | ℕ.*-distrib-∸ʳ (suc a) c b
        | +‿◃ (c ℕ* suc a ∸ b ℕ* suc a)
        = refl
... | no b≰c
  rewrite sign-⊖-≱ b≰c
        | ∣⊖∣-≱ b≰c
        | -‿◃ ((b ∸ c) ℕ* suc a)
        | ⊖-≱ (b≰c ∘ ℕ.cancel-*-right-≤ b c a)
        | ℕ.*-distrib-∸ʳ (suc a) b c
        = refl

distribʳ (+ suc c) (+ suc a) -[1+ b ]
  rewrite +-⊖-left-cancel c (a ℕ* suc c) (b ℕ* suc c)
  with b ≤? a
... | yes b≤a
  rewrite ⊖-≥ b≤a
        | ⊖-≥ (b≤a *-mono ≤-refl {x = suc c})
        | +‿◃ ((a ∸ b) ℕ* suc c)
        | ℕ.*-distrib-∸ʳ (suc c) a b
        = refl
... | no b≰a
  rewrite sign-⊖-≱ b≰a
        | ∣⊖∣-≱ b≰a
        | ⊖-≱ (b≰a ∘ ℕ.cancel-*-right-≤ b a c)
        | -‿◃ ((b ∸ a) ℕ* suc c)
        | ℕ.*-distrib-∸ʳ (suc c) b a
        = refl

-- The IsCommutativeSemiring module contains a proof of
-- distributivity which is used below.

isCommutativeSemiring : IsCommutativeSemiring _≡_ _+_ _*_ (+ 0) (+ 1)
isCommutativeSemiring = record
  { +-isCommutativeMonoid = +-isCommutativeMonoid
  ; *-isCommutativeMonoid = *-isCommutativeMonoid
  ; distribʳ              = distribʳ
  ; zeroˡ                 = λ _ → refl
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
  ; isCommutativeRing = record
    { isRing = record
      { +-isAbelianGroup = +-isAbelianGroup
      ; *-isMonoid       = *-isMonoid
      ; distrib          = IsCommutativeSemiring.distrib
                             isCommutativeSemiring
      }
    ; *-comm = *-comm
    }
  }

import Algebra.RingSolver.Simple as Solver
import Algebra.RingSolver.AlmostCommutativeRing as ACR
module RingSolver =
  Solver (ACR.fromCommutativeRing commutativeRing) _≟_

------------------------------------------------------------------------
-- More properties

-- Multiplication is right cancellative for non-zero integers.

cancel-*-right : ∀ i j k →
                 k ≢ + 0 → i * k ≡ j * k → i ≡ j
cancel-*-right i j k            ≢0 eq with signAbs k
cancel-*-right i j .(+ 0)       ≢0 eq | s ◂ zero  = contradiction refl ≢0
cancel-*-right i j .(s ◃ suc n) ≢0 eq | s ◂ suc n
  with ∣ s ◃ suc n ∣ | abs-◃ s (suc n) | sign (s ◃ suc n) | sign-◃ s n
...  | .(suc n)      | refl            | .s               | refl =
  ◃-cong (sign-i≡sign-j i j eq) $
         ℕ.cancel-*-right ∣ i ∣ ∣ j ∣ $ abs-cong eq
  where
  sign-i≡sign-j : ∀ i j →
                  sign i S* s ◃ ∣ i ∣ ℕ* suc n ≡
                  sign j S* s ◃ ∣ j ∣ ℕ* suc n →
                  sign i ≡ sign j
  sign-i≡sign-j i              j              eq with signAbs i | signAbs j
  sign-i≡sign-j .(+ 0)         .(+ 0)         eq | s₁ ◂ zero   | s₂ ◂ zero   = refl
  sign-i≡sign-j .(+ 0)         .(s₂ ◃ suc n₂) eq | s₁ ◂ zero   | s₂ ◂ suc n₂
    with ∣ s₂ ◃ suc n₂ ∣ | abs-◃ s₂ (suc n₂)
  ... | .(suc n₂) | refl
    with abs-cong {s₁} {sign (s₂ ◃ suc n₂) S* s} {0} {suc n₂ ℕ* suc n} eq
  ...   | ()
  sign-i≡sign-j .(s₁ ◃ suc n₁) .(+ 0)         eq | s₁ ◂ suc n₁ | s₂ ◂ zero
    with ∣ s₁ ◃ suc n₁ ∣ | abs-◃ s₁ (suc n₁)
  ... | .(suc n₁) | refl
    with abs-cong {sign (s₁ ◃ suc n₁) S* s} {s₁} {suc n₁ ℕ* suc n} {0} eq
  ...   | ()
  sign-i≡sign-j .(s₁ ◃ suc n₁) .(s₂ ◃ suc n₂) eq | s₁ ◂ suc n₁ | s₂ ◂ suc n₂
    with ∣ s₁ ◃ suc n₁ ∣ | abs-◃ s₁ (suc n₁)
       | sign (s₁ ◃ suc n₁) | sign-◃ s₁ n₁
       | ∣ s₂ ◃ suc n₂ ∣ | abs-◃ s₂ (suc n₂)
       | sign (s₂ ◃ suc n₂) | sign-◃ s₂ n₂
  ... | .(suc n₁) | refl | .s₁ | refl | .(suc n₂) | refl | .s₂ | refl =
    SignProp.cancel-*-right s₁ s₂ (sign-cong eq)

-- Multiplication with a positive number is right cancellative (for
-- _≤_).

cancel-*-+-right-≤ : ∀ m n o → m * + suc o ≤ n * + suc o → m ≤ n
cancel-*-+-right-≤ (-[1+ m ]) (-[1+ n ]) o (-≤- n≤m) =
  -≤- (≤-pred (ℕ.cancel-*-right-≤ (suc n) (suc m) o (s≤s n≤m)))
cancel-*-+-right-≤ -[1+ _ ]   (+ _)      _ _         = -≤+
cancel-*-+-right-≤ (+ 0)      -[1+ _ ]   _ ()
cancel-*-+-right-≤ (+ suc _)  -[1+ _ ]   _ ()
cancel-*-+-right-≤ (+ 0)      (+ 0)      _ _         = +≤+ z≤n
cancel-*-+-right-≤ (+ 0)      (+ suc _)  _ _         = +≤+ z≤n
cancel-*-+-right-≤ (+ suc _)  (+ 0)      _ (+≤+ ())
cancel-*-+-right-≤ (+ suc m)  (+ suc n)  o (+≤+ m≤n) =
  +≤+ (ℕ.cancel-*-right-≤ (suc m) (suc n) o m≤n)

-- Multiplication with a positive number is monotone.

*-+-right-mono : ∀ n → (λ x → x * + suc n) Preserves _≤_ ⟶ _≤_
*-+-right-mono _ (-≤+             {n = 0})         = -≤+
*-+-right-mono _ (-≤+             {n = suc _})     = -≤+
*-+-right-mono x (-≤-                         n≤m) =
  -≤- (≤-pred (s≤s n≤m *-mono ≤-refl {x = suc x}))
*-+-right-mono _ (+≤+ {m = 0}     {n = 0}     m≤n) = +≤+ m≤n
*-+-right-mono _ (+≤+ {m = 0}     {n = suc _} m≤n) = +≤+ z≤n
*-+-right-mono _ (+≤+ {m = suc _} {n = 0}     ())
*-+-right-mono x (+≤+ {m = suc _} {n = suc _} m≤n) =
  +≤+ (m≤n *-mono ≤-refl {x = suc x})
