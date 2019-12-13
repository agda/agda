-- Andreas, 2019-07-11, issue #3843, reported by shinji-kono
-- recordExpressionToCopattern translation invalidates projection-likeness.

-- {-# OPTIONS -v tc.proj.like:100 -v impossible:10 #-}

data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

postulate
  ANY  : ∀{a} {A : Set a} → A
  Nat  : Set
  suc  : Nat → Nat
  diag : (x : Nat) → x ≡ x
  P    : Nat → Set
  Foo  : {x : Nat} (px : P x) → Set

record Pack (n : Nat) : Set where
  constructor pack
  field
    lv  : Nat
    ord : P lv
open Pack

-- Projection-like, because eta-contracted to  pidproj x = x
pidproj : ∀ {n} (x : Pack n) → Pack n
pidproj x = record { lv = lv x; ord = ord x }

-- Not considered projection-like, since
-- `pidpc (pack l o)` is stuck, but the `n` cannot be inferred.
pidpc : ∀ {n} (x : Pack n) → Pack n
pidpc x .lv = lv x
pidpc x .ord = ord x

-- Not considered projection-like, since
-- `pidcop (pack l o)` is stuck, but the `n` cannot be inferred.
pidcop : ∀ {n} (x : Pack n) → Pack n
pidcop (pack lx ox) .lv  = lx
pidcop (pack lx ox) .ord = ox

-- WAS: Projection-like function,
-- but since is translated to pidcop by recordExpressionsToCopatterns
-- projection-likeness is unsound here.
pid : ∀ {n} (x : Pack n) → Pack n
pid (pack lx ox) = record { lv = lx ; ord = ox }
-- pid record { lv = lx ; ord = ox } = record { lv = lx ; ord = ox }
-- pid (pack lx ox) = pack lx ox  -- no error
-- pid x = x  -- Error disappears with record pattern matching

test : ∀ {n} (x : Pack (suc n)) → x ≡ pid x
test {n} x@(pack lx ox) with diag (lv x)  -- The @-pattern is needed for 2.5.2 and 2.5.3
... | refl with Foo (ord x) -- with needed
... | _ = ANY

-- WAS: internal error

-- Should succeed.
