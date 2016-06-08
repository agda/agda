
-- {-# OPTIONS -v tc.mod.apply:80 #-}

module Issue1985 where

module Def where
  postulate A : Set

module Par (X : Set₁) where
  postulate B : Set
  open Def public

-- module Works where
--   module Ren B = Par B
--   module App = Ren Set

module Fails where
  module RenP (X : Set₁) = Par X
  module Ren = Par
  -- Like RenP, Ren should contain
  --   A : (B : Set) → Set
  --   A B = Par.A B
  -- but it incorrectly contained
  --   A : Set
  --   A = Par.A

  A₁ A₂ B₁ B₂ : Set₁ → Set
  A₁ = RenP.A
  A₂ = Ren.A
  B₁ = RenP.B
  B₂ = Ren.B

  module App = Ren Set

  A₃ B₃ : Set
  A₃ = App.A
  B₃ = App.B
