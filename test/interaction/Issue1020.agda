-- Andreas, 2014-01-10, reported by fredrik.forsberg

record ⊤ : Set where

record Σ (A : Set) (B : A → Set) : Set  where

syntax Σ A (λ x → B) = Σ[ x ∈ A ] B

test : Set
test = {! Σ[ x ∈ ⊤ ] ?!}

-- Fredrik's report:

-- Using the darcs version of Agda from today 10 January,
-- if I load the file and give (or refine) in the hole, I end up with
--
--   test = Σ ⊤ (λ x → {!!})
--
-- i.e. Agda has translated away the syntax Σ[ x ∈ ⊤ ] {!!} for me. I would of course
-- expect
--
--   test = Σ[ x ∈ ⊤ ] {!!}
--
-- instead, and I think this used to be the behaviour? (Using the Σ from
-- the standard library, this is more annoying, as one gets
--
--   test = Σ-syntax ⊤ (λ x → {!!})
--
-- as a result.)
--
-- This might be related to issue 994?


-- Expected test case behavior:
--
-- Bad (at the time of report:
--
--   (agda2-give-action 0 "Σ ⊤ (λ x → ?)")
--
-- Good:
--
--   (agda2-give-action 0 'no-paren)
