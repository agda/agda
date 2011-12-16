------------------------------------------------------------------------
-- The Agda standard library
--
-- Some properties about integers
------------------------------------------------------------------------

module Data.Integer.Properties where

open import Algebra
open import Algebra.Structures
import Algebra.Morphism as Morphism
open import Data.Integer hiding (suc; _≤?_; _≤_)
open import Data.Nat using (ℕ; suc; zero; _∸_; _≤?_; _≤_; _<_; _≰_; s≤s; z≤n)
                     renaming (_+_ to _ℕ+_; _*_ to _ℕ*_)
open import Data.Nat.Properties using (_*-mono_)
open import Data.Product using (proj₁; proj₂; _,_)
open import Data.Sign as Sign using () renaming (_*_ to _S*_)
import Data.Sign.Properties as SignProp
open import Function using (_∘_; _$_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

import Data.Nat.Properties as ℕ
open Data.Nat.Properties.SemiringSolver
import Algebra.FunctionProperties as FP; open FP (_≡_ {A = ℤ})

open ≡-Reasoning
open Morphism.Definitions ℤ ℕ _≡_

open CommutativeSemiring Data.Nat.Properties.commutativeSemiring using ()
  renaming (zero to *-zero; distrib to *-distrib)

import Data.Integer.Addition.Properties as AP
open CommutativeMonoid AP.commutativeMonoid using ()
  renaming (assoc to +-assoc; comm to +-comm; identity to +-identity;
            isCommutativeMonoid to +-isCommutativeMonoid; isMonoid to +-isMonoid)


import Data.Integer.Multiplication.Properties as MP
open CommutativeMonoid MP.commutativeMonoid using ()
  renaming (assoc to *-assoc; comm to *-comm; identity to *-identity;
            isCommutativeMonoid to *-isCommutativeMonoid; isMonoid to *-isMonoid)

open DecTotalOrder Data.Nat.decTotalOrder using () renaming (refl to ≤-refl)

private

  --------------------------------------------------------
  -- These functions help to rewrite _⊖_ into _∸_
  -- The behavior of a ⊖ b depends on a ≤ b, and _∸_ is
  -- much easier to reason about.

  ≰sign : ∀ {a b} → a ≰ b → sign (b ⊖ a) ≡ Sign.-
  ≰sign = aux ∘ ℕ.≰⇒>
    where
    aux : ∀ {a b} → b < a → sign (b ⊖ a) ≡ Sign.-
    aux .{_} {zero} (s≤s z≤n) = refl
    aux .{suc n'} {suc n} (s≤s {.(suc n)} {n'} m≤n) = aux m≤n


  -abs : ∀ {a b} → a ≰ b → ∣ b ⊖ a ∣ ≡ a ∸ b
  -abs = aux ∘ ℕ.≰⇒>
    where
    aux : ∀ {a b} → a < b → ∣ a ⊖ b ∣ ≡ b ∸ a
    aux {zero} (s≤s z≤n) = refl
    aux {suc n} (s≤s m≤n) = aux m≤n



  nonnegative-⊖ : ∀ {a b} → b ≤ a → a ⊖ b ≡ + (a ∸ b)
  nonnegative-⊖ z≤n = refl
  nonnegative-⊖ (s≤s m≤n) = nonnegative-⊖ m≤n


  negative-⊖ : ∀ {a b} → b ≰ a → a ⊖ b ≡ - (+ (b ∸ a))
  negative-⊖ = aux ∘ ℕ.≰⇒>
    where
    aux : ∀ {a b} → a < b → a ⊖ b ≡ - (+ (b ∸ a))
    aux {zero} (s≤s z≤n) = refl
    aux {suc n} (s≤s m≤n) = aux m≤n

  -- Because the first case of _◃_ involves checking for zero,
  -- most proves involving this operator, but not casing on the
  -- second argument, will need the following lemmas

  +‿◃ : ∀ n → Sign.+ ◃ n ≡ + n
  +‿◃ zero = refl
  +‿◃ (suc n) = refl

  -‿◃ : ∀ n → Sign.- ◃ n ≡ - (+ n)
  -‿◃ zero = refl
  -‿◃ (suc n) = refl


  +-⊖-left-cancel : ∀ a b c → (a ℕ+ b) ⊖ (a ℕ+ c) ≡ b ⊖ c
  +-⊖-left-cancel zero b c = refl
  +-⊖-left-cancel (suc a) b c = +-⊖-left-cancel a b c

  ⊖-swap : ∀ a b → a ⊖ b ≡ - (b ⊖ a)
  ⊖-swap zero zero = refl
  ⊖-swap (suc _) zero = refl
  ⊖-swap zero (suc _) = refl
  ⊖-swap (suc a) (suc b) = ⊖-swap a b


  -‿cancel : Involutive -_
  -‿cancel -[1+ n ] = refl
  -‿cancel (+ zero) = refl
  -‿cancel (+ suc _) = refl


  -- This logic is extracted from the main distrib proof because it is shared
  -- between two cases.

  distrib-lemma : ∀ a b c → (c ⊖ b) * -[1+ a ] ≡ a ℕ+ b ℕ* suc a ⊖ (a ℕ+ c ℕ* suc a)
  distrib-lemma a b c
    rewrite +-⊖-left-cancel a (b ℕ* suc a) (c ℕ* suc a)
          | ⊖-swap (b ℕ* suc a) (c ℕ* suc a)
     with b ≤? c
  ... | yes b≤c rewrite
        nonnegative-⊖ b≤c
      | nonnegative-⊖ (b≤c *-mono (≤-refl {x = suc a}))
      | -‿◃ ((c ∸ b) ℕ* suc a)
      | ℕ.*-distrib-∸ʳ (suc a) c b
      = refl

  ... | no b≰c rewrite
        ≰sign b≰c
      | -abs b≰c
      | +‿◃ ((b ∸ c) ℕ* suc a)
      | negative-⊖ (b≰c ∘ ℕ.cancel-*-right-≤ b c a)
      | -‿cancel (+ (b ℕ* suc a ∸ c ℕ* suc a))
      | ℕ.*-distrib-∸ʳ (suc a) b c
      = refl


  distribʳ : _*_ DistributesOverʳ _+_

  distribʳ (+ zero) y z rewrite proj₂ *-zero ∣ y ∣
                                | proj₂ *-zero ∣ z ∣
                                | proj₂ *-zero ∣ y + z ∣ = refl

  distribʳ x (+ zero) z
    rewrite proj₁ +-identity z
          | proj₁ +-identity (sign z S* sign x ◃ ∣ z ∣ ℕ* ∣ x ∣)
          = refl

  distribʳ x y (+ zero)
    rewrite proj₂ +-identity y
          | proj₂ +-identity (sign y S* sign x ◃ ∣ y ∣ ℕ* ∣ x ∣)
          = refl

  distribʳ -[1+ a ] -[1+ b ] -[1+ c ]  = cong +_ $
    solve 3 (λ a b c → (con 2 :+ b :+ c) :* (con 1 :+ a)
                    := (con 1 :+ b) :* (con 1 :+ a) :+ (con 1 :+ c) :* (con 1 :+ a))
            refl a b c

  distribʳ (+ suc a) (+ suc b) (+ suc c) = cong +_ $
    solve 3 (λ a b c → (con 1 :+ b :+ (con 1 :+ c)) :* (con 1 :+ a)
                    := (con 1 :+ b) :* (con 1 :+ a) :+ (con 1 :+ c) :* (con 1 :+ a))
          refl a b c

  distribʳ -[1+ a ] (+ suc b) (+ suc c) = cong -[1+_] $
    solve 3 (λ a b c → a :+ (b :+ (con 1 :+ c)) :* (con 1 :+ a)
                     := (con 1 :+ b) :* (con 1 :+ a) :+ (a :+ c :* (con 1 :+ a)))
           refl a b c

  distribʳ (+ suc a) -[1+ b ] -[1+ c ] = cong -[1+_] $
    solve 3 (λ a b c → a :+ (con 1 :+ a :+ (b :+ c) :* (con 1 :+ a))
                    := (con 1 :+ b) :* (con 1 :+ a) :+ (a :+ c :* (con 1 :+ a)))
           refl a b c

  distribʳ -[1+ a ] -[1+ b ] (+ suc c) = distrib-lemma a b c

  distribʳ -[1+ a ] (+ suc b) -[1+ c ] = distrib-lemma a c b

  distribʳ (+ suc a) -[1+ b ] (+ suc c)
     rewrite +-⊖-left-cancel a (c ℕ* suc a) (b ℕ* suc a)

     with b ≤? c
  ... | yes b≤c rewrite
        nonnegative-⊖ b≤c
      | +-comm (- (+ (a ℕ+ b ℕ* suc a))) (+ (a ℕ+ c ℕ* suc a))
      | nonnegative-⊖ (b≤c *-mono ≤-refl {x = suc a})
      | ℕ.*-distrib-∸ʳ (suc a) c b
      | +‿◃ (c ℕ* suc a ∸ b ℕ* suc a)
      = refl

  ... | no b≰c rewrite
        ≰sign b≰c
      | -abs b≰c
      | -‿◃ ((b ∸ c) ℕ* suc a)
      | negative-⊖ (b≰c ∘ ℕ.cancel-*-right-≤ b c a)
      | ℕ.*-distrib-∸ʳ (suc a) b c
      = refl

  distribʳ (+ suc c) (+ suc a) -[1+ b ]
    rewrite +-⊖-left-cancel c (a ℕ* suc c) (b ℕ* suc c)

    with b ≤? a
  ... | yes b≤a rewrite
        nonnegative-⊖ b≤a
      | nonnegative-⊖ (b≤a *-mono ≤-refl {x = suc c})
      | +‿◃ ((a ∸ b) ℕ* suc c)
      | ℕ.*-distrib-∸ʳ (suc c) a b
      = refl

  ... | no b≰a rewrite
        ≰sign b≰a
      | -abs b≰a
      | negative-⊖ (b≰a ∘ ℕ.cancel-*-right-≤ b a c)
      | -‿◃ ((b ∸ a) ℕ* suc c)
      | ℕ.*-distrib-∸ʳ (suc c) b a
      = refl

isCommutativeSemiring : IsCommutativeSemiring _≡_ _+_ _*_ (+ 0) (+ 1)
isCommutativeSemiring = record {
                          +-isCommutativeMonoid = +-isCommutativeMonoid;
                          *-isCommutativeMonoid = *-isCommutativeMonoid;
                          distribʳ = distribʳ;
                          zeroˡ = λ x → refl }

-- just using this to get distrib for free...
commutativeSemiring : CommutativeSemiring _ _
commutativeSemiring = record {
                        Carrier = ℤ;
                        _≈_ = _≡_;
                        _+_ = _+_;
                        _*_ = _*_;
                        0# = + 0;
                        1# = + 1;
                        isCommutativeSemiring = isCommutativeSemiring }

n⊖n≡0 : ∀ n → n ⊖ n ≡ + 0
n⊖n≡0 zero = refl
n⊖n≡0 (suc n) = n⊖n≡0 n

private
  inverseˡ : LeftInverse (+ 0) -_ _+_
  inverseˡ -[1+ n ] = n⊖n≡0 n
  inverseˡ (+ zero) = refl
  inverseˡ (+ suc n) = n⊖n≡0 n

  inverseʳ : RightInverse (+ 0) -_ _+_
  inverseʳ -[1+ n ] = n⊖n≡0 n
  inverseʳ (+ zero) = refl
  inverseʳ (+ suc n) = n⊖n≡0 n

isGroup : IsGroup _≡_ _+_ (+ 0) -_
isGroup = record
  { isMonoid = +-isMonoid
  ; inverse = inverseˡ , inverseʳ
  ; ⁻¹-cong = cong -_
  }

isAbelianGroup : IsAbelianGroup _≡_ _+_ (+ 0) -_
isAbelianGroup = record
  { isGroup = isGroup
  ; comm    = +-comm
  }

isRing : IsRing _≡_ _+_ _*_ -_ (+ 0) (+ 1)
isRing = record
  { +-isAbelianGroup = isAbelianGroup
  ; *-isMonoid       = *-isMonoid
  ; distrib          = CommutativeSemiring.distrib commutativeSemiring
  }

isCommutativeRing : IsCommutativeRing _≡_ _+_ _*_ -_ (+ 0) (+ 1)
isCommutativeRing = record
  { isRing = isRing
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
  ; isCommutativeRing = isCommutativeRing
  }

import Algebra.RingSolver.Simple as Solver
import Algebra.RingSolver.AlmostCommutativeRing as ACR
module RingSolver =
  Solver (ACR.fromCommutativeRing commutativeRing)

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
