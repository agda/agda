-- Andreas, 2026-05-09, issue #8559, duplicate of #3054
-- Report and test case by Nate Soares
-- Regression introduced in 2.6.0 by fix of #2964

data _≡_ {A : Set} (a : A) : A → Set where
    refl : a ≡ a

data Bool : Set where
    false true : Bool

data _≤_ : Bool → Bool → Set where
    false≤ : ∀ b → false ≤ b
    true≤ : true ≤ true

id : ∀ b → b ≤ b
id false = false≤ false
id true = true≤

record IsSieve (B : Bool → Set) : Set where
    field
        sift : ∀ {a b} → a ≤ b → B b → B a
        sift-id : ∀ a (x : B a) → x ≡ sift (id a) x

data F : Bool → Set where
    ffalse : F false
    ftrue : F true

sift-F : ∀ {a b} → a ≤ b → F b → F a
sift-F {false} {false} _ x = x
sift-F {false} {true} _ ftrue = ffalse
sift-F {true} {true} _ x = x

Works : IsSieve F
Works .IsSieve.sift = sift-F
Works .IsSieve.sift-id false _ = refl
Works .IsSieve.sift-id true _ = refl

Breaks : IsSieve F
Breaks .IsSieve.sift {false} {false} _ x = x
Breaks .IsSieve.sift {false} {true} _ ftrue = ffalse   -- (2)
Breaks .IsSieve.sift {true} {true} _ x = x             -- (3)
Breaks .IsSieve.sift-id false _ = refl
Breaks .IsSieve.sift-id true _ = refl                  -- (5)

-- WAS: last refl (5) failed because clause (3) did not fire during lhs checking,
-- only after coverage checking.
-- Firing (3) was blocked by the match ftrue/x in clause (2) that since the fix of #2964
-- resulted in a "DontKnow" even though the prior match false/true is a hard "No".

-- NOW: succeeds.
-- We only turn "No" into "DontKnow" now if the "DontKnow" has a higher priority,
-- i.e. if in the resulting case tree split it could precede the "No".
