-- Andreas, 2017-10-02, issue #2785, reported by ...

-- {-# OPTIONS -v scope.extendedLambda:100 #-}

{-# OPTIONS --allow-unsolved-metas #-}

foo : _
foo = {!foo λ {x y → foo}!}  -- C-c C-r

-- Upon refine (C-c C-r), error was:
--
-- An internal error has occurred. Please report this as a bug.
-- Location of the error: src/full/Agda/Syntax/Translation/ConcreteToAbstract.hs:721

-- Now: unsolved metas and constraints.
