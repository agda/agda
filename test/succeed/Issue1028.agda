-- 2014-09-19
-- Reported by Mateusz Kowalczyk.

good : Set₁
good = let -- F : _  -- worked if you added the type signature
           F X = X
       in F Set

-- Now works without the type signature.
