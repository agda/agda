-- Andreas, 2016-06-08
-- Better error message when case splitting is invoked in location
-- where there is nothing to split

record R : Set where
  field f : {!!}

-- C-c C-c RET here gives:
-- Cannot split here, as we are not in a function definition
