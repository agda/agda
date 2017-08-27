-- Andreas, 2017-08-24, issue #2717, reported by m0davis
--
-- Internal error in DisplayForm.hs triggered by -v 100.
-- Regression introduced by #2590

{-# OPTIONS -v tc.display.top:100 -v tc.polarity.dep:20 #-} -- KEEP

module _ (A : Set) where

module M (_ : Set) where
  data D (n : Set) : Set where
    d : D n

open M A
