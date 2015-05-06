-- Andreas, 2015-05-06 issue reported by andor.penzes@prezi.com

record CoList : Set

data   CoList : Set where

record CoList where

-- Error WAS:
-- An internal error has occurred. Please report this as a bug.
-- Location of the error: src/full/Agda/Syntax/Concrete/Definitions.hs:479

-- Error should be:
-- Duplicate definition of CoList
