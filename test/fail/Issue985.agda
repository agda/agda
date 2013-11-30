-- {-# OPTIONS -v tc.cover.split.con:20 #-}

open import Common.Prelude renaming (Nat to ℕ)
open import Common.Equality

infix 3 ¬_

¬_ : Set → Set
¬ P = P → ⊥

-- Decidable relations.

data Dec (P : Set) : Set where
  yes : ( p :   P) → Dec P
  no  : (¬p : ¬ P) → Dec P

_≟_ : (m n : ℕ) → Dec (m ≡ n)
zero  ≟ zero   = yes refl
zero  ≟ suc n  = no λ()
suc m ≟ zero   = no λ()
suc m ≟ suc n  with m ≟ n
suc m ≟ suc .m | yes refl = yes refl
suc m ≟ suc n  | no prf   = no (λ x → prf (cong pred x))

data Ty : Set where

data Cxt : Set where
  ε   : Cxt
  _,_ : (Γ : Cxt) (a : Ty) → Cxt

len : Cxt → ℕ
len ε       = 0
len (Γ , _) = suc (len Γ)

-- De Bruijn index

mutual
  Var : Cxt → Ty → Set
  Var Γ a = Var' a Γ

  data Var' (a : Ty) : (Γ : Cxt) → Set where
    zero : ∀ {Γ}                 → Var (Γ , a) a
    suc  : ∀ {Γ b} (x : Var Γ a) → Var (Γ , b) a

-- De Bruijn Level

Lev = ℕ

-- Valid de Bruijn levels.

data LookupLev : (x : Lev) (Γ : Cxt) (a : Ty) (i : Var Γ a) → Set where
  lookupZero : ∀ {Γ a} →
    LookupLev (len Γ) (Γ , a) a zero

  lookupSuc : ∀ {Γ a b x i} →
    LookupLev x Γ a i →
    LookupLev x (Γ , b) a (suc i)

record ValidLev (x : Lev) (Γ : Cxt) : Set where
  constructor validLev
  field
    {type } : Ty
    {index} : Var Γ type
    valid   : LookupLev x Γ type index

weakLev : ∀ {x Γ a} → ValidLev x Γ → ValidLev x (Γ , a)
weakLev (validLev d) = validLev (lookupSuc d)

-- Looking up a de Bruijn level.

lookupLev : ∀ (x : Lev) (Γ : Cxt) → Dec (ValidLev x Γ)
lookupLev x ε = no λ { (validLev ()) }
lookupLev x (Γ , a) with x ≟ len Γ
lookupLev ._ (Γ , a) | yes refl = yes (validLev lookupZero)
lookupLev x (Γ , a) | no _ with lookupLev x Γ
lookupLev x (Γ , a) | no ¬p | yes d = yes (weakLev d)
lookupLev x (Γ , a) | no ¬p | no ¬d = no contra
  where
    contra : ¬ ValidLev x (Γ , a)
    contra (validLev (lookupSuc valid)) = ?

{- Unbound indices showing up in error message:

I'm not sure if there should be a case for the constructor
lookupZero, because I get stuck when trying to solve the following
unification problems (inferred index ≟ expected index):
  len Γ ≟ @8
  Γ , a ≟ @7 , @4
  a ≟ type
  zero ≟ index
when checking the definition of contra -}
