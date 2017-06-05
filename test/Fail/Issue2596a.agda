{-# OPTIONS -W error #-}
module Issue2596a where

{-# REWRITE #-}

-- We will never encounter this, because the harmless warning above
-- has been turned into an error
f : Set
f = f
