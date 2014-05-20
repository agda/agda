-- Andreas, 2014-05-20, issue reported by Fabien Renaud

module Issue1125 where

f : {A- : Set} -> Set
f {A-} = A-

-- Should give a parse error now
-- since a comment is closed -} but none opened.

