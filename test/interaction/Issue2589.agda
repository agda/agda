
open import Agda.Builtin.Nat

-- splitting on a 'with' argument should not expand the ellipsis
foo : Nat → Nat
foo m with 0
... | n = {!n!}

-- splitting on variable hidden by ellipsis should expand the ellipsis
bar : Nat → Nat
bar m with 0
... | n = {!m!}

-- test case with nested with
baz : Nat → Nat
baz m with m
... | n with n
... | p = {!p!}

-- data IsSuc : Nat → Set where
--   isSuc : ∀ n → IsSuc (suc n)

-- postulate
--   lie : ∀ n → IsSuc n

-- blub : Nat → Nat → Nat
-- blub x y with lie x | bar y
-- ... | isSuc n | q with lie q | lie x
-- ... | r | isSuc _ = {!r!}
