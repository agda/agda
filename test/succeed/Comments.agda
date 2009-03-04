module Comments where

{- Single-line comments cannot be started inside multi-line ones:

-- -} postulate
        foo : Set

-- The following comment marker is followed by an alphabetic
-- character:

--This is a {- non-nested comment.
{-This is a comment.-}

{-
-- The final comment marker {- is followed by -} the end of the file
-- without any intervening newline.
-}

--