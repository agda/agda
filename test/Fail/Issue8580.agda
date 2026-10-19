-- Andreas, 2026-06-04, issue #8580, reported and test by DrpontAgon
-- Pattern synonym checking crashed if argument was _.

-- {-# OPTIONS -v scope.pat:40 #-}

pattern S _ = Set

-- WAS: internal error
--
-- Expected error: [UnusedVariableInPatternSynonym]
-- Unused variable in pattern synonym: _
-- when scope checking the declaration
--   pattern S _ = Set
