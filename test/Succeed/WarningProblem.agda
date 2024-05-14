-- Andreas, 2024-04-13, issue #7219
-- Switch of reporting warning problems (WarningProblem).

{-# OPTIONS -WnoTerminationIssue -W ThisIsAnUnknownWarning -WnoWarningProblem #-}

-- Should succeed without warnings.
