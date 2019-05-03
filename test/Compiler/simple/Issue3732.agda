-- Andreas, 2019-05-03, issue #3732
--
-- Do not erase constructor arguments when bound to Haskell data type.
-- Otherwise, it is not predictable how the Haskell constructors should look like.

-- {-# OPTIONS -v compile:100 #-}

open import Agda.Builtin.IO
open import Agda.Builtin.Unit

{-# FOREIGN GHC data I = Bar #-}
{-# FOREIGN GHC data S = Foo I #-}

module NonMutual where

  data I : Set where
    bar : I

  {-# COMPILE GHC I = data I (Bar) #-}

  data S : Set where
    foo :  (i : I) → S

  {-# COMPILE GHC S = data S (Foo) #-}

-- It could be that an earlier type embeds a later type, by virtue of mutual blocks:

{-# FOREIGN GHC data I2 = Bar2 #-}
{-# FOREIGN GHC data S2 = Foo2 I2 #-}

module Mutual where

 mutual

  data S : Set where
    foo :  (i : I) → S

  {-# COMPILE GHC S = data S2 (Foo2) #-}

  data I : Set where
    bar : I

  {-# COMPILE GHC I = data I2 (Bar2) #-}

postulate
  main : IO ⊤

{-# COMPILE GHC main = return () #-}
