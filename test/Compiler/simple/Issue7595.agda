-- Regression test for #7595: nested with must not duplicate the outer case tree.

open import Agda.Builtin.Maybe
open import Common.IO
open import Common.Unit

case_of_ : {A B : Set} → A → (A → B) → B
case x of f = f x

data Cell : Set where
  [-] [o] [x] : Cell

data Board : Set where
  mk-Board :
    (_ _ _
     _ _ _
     _ _ _ : Cell) → Board

winner : Board → Maybe Cell
winner = λ where
  (mk-Board [x]  _   _
            [x]  _   _
            [x]  _   _) → just [x]

  (mk-Board  _  [x]  _
             _  [x]  _
             _  [x]  _) → just [x]

  (mk-Board  _   _  [x]
             _   _  [x]
             _   _  [x]) → just [x]

  (mk-Board [x] [x] [x]
             _   _   _
             _   _   _ ) → just [x]

  (mk-Board  _   _   _
            [x] [x] [x]
             _   _   _ ) → just [x]

  (mk-Board  _   _   _
             _   _   _
            [x] [x] [x]) → just [x]

  (mk-Board [x]  _   _
             _  [x]  _
             _   _  [x]) → just [x]

  (mk-Board  _   _  [x]
             _  [x]  _
            [x]  _   _ ) → just [x]

  (mk-Board [o]  _   _
            [o]  _   _
            [o]  _   _ ) → just [o]

  (mk-Board  _  [o]  _
             _  [o]  _
             _  [o]  _ ) → just [o]

  (mk-Board  _   _  [o]
             _   _  [o]
             _   _  [o]) → just [o]

  (mk-Board [o] [o] [o]
             _   _   _
             _   _   _ ) → just [o]

  (mk-Board  _   _   _
            [o] [o] [o]
             _   _   _ ) → just [o]

  (mk-Board  _   _   _
             _   _   _
            [o] [o] [o]) → just [o]

  (mk-Board [o]  _   _
              _  [o]  _
              _   _  [o]) → just [o]

  (mk-Board  _   _  [o]
             _  [o]  _
            [o]  _   _ ) → just [o]

  (mk-Board [-]  _   _
             _   _   _
             _   _   _ ) → nothing

  (mk-Board  _  [-]  _
             _   _   _
             _   _   _ ) → nothing

  (mk-Board  _   _  [-]
             _   _   _
             _   _   _ ) → nothing

  (mk-Board  _   _   _
            [-]  _   _
             _   _   _ ) → nothing

  (mk-Board  _   _   _
             _  [-]  _
             _   _   _ ) → nothing

  (mk-Board  _   _   _
             _   _  [-]
             _   _   _ ) → nothing

  (mk-Board  _   _   _
             _   _   _
            [-]  _   _ ) → nothing

  (mk-Board  _   _   _
             _   _   _
             _  [-]  _ ) → nothing

  (mk-Board  _   _   _
             _   _   _
             _   _  [-]) → nothing

  (mk-Board  _   _   _
             _   _   _
             _   _   _ ) → just [-]

b0 : Board
b0 = mk-Board
  [-] [-] [-]
  [-] [-] [-]
  [-] [-] [-]

step1 : Board → Board
step1 b = case winner b of λ where
  (just _) → b
  nothing → b0

step2 : Board → Board
step2 b with winner b
... | just _ = b
... | nothing = b0

-- The fixed module is about 125 KB, while the regression produced 114 MB.
-- Check the generated entry module with enough headroom for ordinary changes.
postulate checkGeneratedSize : IO Unit

{-# COMPILE JS checkGeneratedSize =
    cb => {
      import("node:fs").then(fs => {
        const size = fs.statSync(process.argv[1]).size;
        if (size > 1000000) {
          process.stderr.write(
            "generated JavaScript exceeds 1000000 bytes: " + size + "\n");
          process.exitCode = 1;
          return;
        }
        cb(0);
      });
    }
#-}

main : IO Unit
main = checkGeneratedSize >>= \ _ -> putStr "OK\n"
