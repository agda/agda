{-# OPTIONS -W ignore #-}
module Issue2596b where

-- This warning will be ignored
{-# REWRITE #-}

-- but this error will still be raised
f : Set
f = f
