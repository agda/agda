-- 2014-09-19
-- Reported by Mateusz Kowalczyk.

bad : Set₁
bad = let -- F : _  -- works if you add the type signature
          F X = X
      in F Set

-- Bad error: Not in scope: X

-- Better error:
-- Could not parse the left-hand side F X
-- when scope checking let F X = X in F Set
