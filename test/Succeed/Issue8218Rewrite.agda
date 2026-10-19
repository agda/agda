{-# OPTIONS --rewriting #-}

open import Agda.Builtin.List public
open import Issue8218ListUtils

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

{-# REWRITE map-++ #-}
