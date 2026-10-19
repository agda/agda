-- The flag --erased-matches is overridden by --no-erased-matches
-- (even if --no-erased-matches is given first).

{-# OPTIONS --no-erased-matches --erased-matches #-}

F : @0 Set → Set₁
F _ = Set
