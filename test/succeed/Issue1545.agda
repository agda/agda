-- Andreas, 2015-06-17
-- Postponing checkArguments dropped already inserted implicit arguments.

{-# OPTIONS --show-implicit #-}
-- {-# OPTIONS -v tc.def.alias:100 -v tc.decl:10 -v tc.term.expr:20 -v tc.data.con:20 #-}
-- {-# OPTIONS  -v tc.meta.assign:10 #-}
-- {-# OPTIONS  -v tc.term.expr.args:80 #-}
-- {-# OPTIONS  -v tc.term.args:30 #-}

postulate
  S : Set
  Cxt : Set
  N : (Γ : Cxt) → Set

  NeP  : ∀ (i : S) Δ (n : N Δ) → Set
  inhN : ∀ i Δ (v : N Δ) → NeP i Δ v

data Val (Δ : Cxt) : Set where
  ne : ∀ (n : N Δ) → Val Δ

-- BEGIN mutual

data ValP i Δ : (v : Val Δ) → Set
NeO : _

data ValP i Δ where
  cn  : ∀ (n : N Δ) → NeO n i  → ValP i Δ (ne n)
-- adding constructor cn : (n : N Δ) → _24 i Δ n → ValP i Δ (ne n)
-- LATER    : term _24 i Δ n := NeO n i
-- SHOULD BE: term _24 i Δ n := NeO {Δ} i n

-- must be last in mutual block for error
-- implicit argument needed for error
-- NeO_[_] : ∀ {Δ} (n : N Δ) (i : S) → Set  -- full type signature removes error
NeO = λ {Δ} n i → NeP i Δ n

-- END mutual

inhVal : ∀ i Δ (v : Val Δ) → ValP i Δ v
inhVal i Δ (ne n) = cn n (inhN i Δ n)

-- Checking inhN i Δ n : NeO n [ i ] -->  λ i₁ → NeP i₁ n i

-- ANALYSIS:
-- checked type signature NeO : _20
-- checking constructor cn : (n : N Δ) → NeO n i → ValP i Δ (ne n)
-- adding constructor cn : (n : N Δ) → _24 i Δ n → ValP i Δ (ne n)
-- postponed checking arguments [n, i] against _20
-- progress: checked [] remaining [n, i] : _20
-- term _20 :>= {Δ : _27} → _29 {Δ}
-- term _20 :>= {Δ : _27} → _29 {Δ}
-- solving _20 := {Δ : _27} → _29 {Δ}
-- postponed checking arguments [n, i] against _29 {_Δ_30 i Δ n}
-- progress: checked [] remaining [n, i] : _29 {_Δ_30 i Δ n}
-- Checking λ n i → NeP i Δ n : _29 {Δ}
-- solving _29 := λ {Δ} → (n : N Δ) (i : S) → Set
-- solving _24 := (λ i Δ n → NeO n i)
