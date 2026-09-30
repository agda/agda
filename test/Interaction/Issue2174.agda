postulate
  F : Set → Set

G : Set
G = {!F ?!}

-- KEEP COMMENTS AT THE END to not mess with the ranges in Issue2174.sh

-- Andreas, 2016-09-10, issue #2174 reported by Nisse

-- First infer, then give should goalify the questionmark
