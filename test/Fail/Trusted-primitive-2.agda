{-# OPTIONS --erased-quotients #-}

open import Agda.Builtin.Erased.Quotient hiding (qrec)

-- This primitive is trusted, so it is not allowed in this module.

primitive
  qrec : Set
