-- Andreas, 2017-07-29, issue and test case by Nisse

{-# OPTIONS -vprofile:7 #-}

A : Set
A = {!Set!} -- Give to provoke error

-- This issue concerns the AgdaInfo buffer,
-- the behavior on the command line might be different.

-- ERROR WAS (note the "Total 0ms"):
-- Set₁ != Set
-- when checking that the expression Set has type SetTotal 0ms

-- Expected:
-- Set₁ != Set
-- when checking that the expression Set has type Set

-- Issue2602.out:
-- ...
-- ((last . 1) . (agda2-goals-action '(0)))
-- (agda2-verbose "Total 0ms ")
-- (agda2-info-action "*Error*" "1,1-4 Set₁ != Set when checking that the expression Set has type Set" nil)
-- ...
