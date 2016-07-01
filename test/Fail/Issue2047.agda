
postulate anything : ∀{a}{A : Set a} → A

data N : Set where
  suc : (n : N) → N

data Val : (n : N) → Set where
  valSuc : (n : N) → Val (suc n)
--  valSuc : (n : N) → Val n -- internal error disappears

Pred : Set₁
Pred = (n : N) → Set

postulate
  Any  : (P : Pred) → Set
  F    : (P : Pred) → Pred
  anyF : {P : Pred} (S : Any P) → Any (F P)

Evaluate : ∀ (n : N) (P : (w : Val n) → Set) → Set
Evaluate n P = P anything

LR : (n : N) → Pred
LR n m = Evaluate n λ { (valSuc _) → anything}

anyLR : {n : N} → Any (LR n)
anyLR = anyF anything
