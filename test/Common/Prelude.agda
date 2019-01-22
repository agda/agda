{-# OPTIONS --without-K #-}
module Common.Prelude where


import Common.Level

open import Agda.Builtin.Unit public
open import Common.Bool   public
open import Common.Char   public
open import Common.Float  public
open import Common.IO     public
open import Common.List   public
open import Common.Maybe  public
open import Common.Nat    public
open import Common.String public
open import Common.Unit   public

data   ⊥ : Set where
