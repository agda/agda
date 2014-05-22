-- Andreas, 2014-05-22

module _ where

module M where
  f : Set
  f = f

module N where
  f : Set
  f = f

-- OUTPUT IS:
--
-- Termination checking failed for the following functions:
--   f, f
-- Problematic calls:
--   f (at /home/abel/tmp/bla/Agda/test/bugs/TerminationReportQualified.agda:7,7-8)
--   f (at /home/abel/tmp/bla/Agda/test/bugs/TerminationReportQualified.agda:11,7-8)

-- Expected: Qualified names M.f and N.f
