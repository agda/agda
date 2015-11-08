-- Andreas, 2013-06-15 reported by Guillaume Brunerie
-- {-# OPTIONS -v malonzo.definition:100 #-}
module Issue867 where

{- The program below gives the following error when trying to compile it (using MAlonzo)

$ agda -c Test.agda
Checking Test (/tmp/Test.agda).
Finished Test.
Compiling Test in /tmp/Test.agdai to /tmp/MAlonzo/Code/Test.hs
Calling: ghc -O -o /tmp/Test -Werror -i/tmp -main-is MAlonzo.Code.Test /tmp/MAlonzo/Code/Test.hs --make -fwarn-incomplete-patterns -fno-warn-overlapping-patterns
[1 of 2] Compiling MAlonzo.RTE      ( MAlonzo/RTE.hs, MAlonzo/RTE.o )
[2 of 2] Compiling MAlonzo.Code.Test ( /tmp/MAlonzo/Code/Test.hs, /tmp/MAlonzo/Code/Test.o )

Compilation error:

/tmp/MAlonzo/Code/Test.hs:21:35:
    Not in scope: `d5'
    Perhaps you meant one of these:
      `d1' (line 11), `d4' (line 26), `d9' (line 29)
-}


-- Here is the program


module Test where

data ℕ : Set where
  O : ℕ
  S : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

postulate
  IO : ∀ {i} → Set i → Set i
  return : ∀ {i} {A : Set i} → A → IO A

{-# BUILTIN IO IO #-}

main : IO ℕ
main = return (S 1)

{- It’s the first time I try to compile an Agda program, so presumably I’m doing something wrong. But even if I’m doing something wrong, Agda should be the one giving the error, not ghc. -}

-- Should work now.
