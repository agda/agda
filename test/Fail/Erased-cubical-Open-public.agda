{-# OPTIONS --erased-cubical --erasure #-}

-- Modules that use --cubical can be imported when --erased-cubical is
-- used.

open import Erased-cubical-Open-public.Cubical

-- However, re-exports from such modules, made using module
-- application, can only be used in erased contexts.

_ : Set
_ = A
