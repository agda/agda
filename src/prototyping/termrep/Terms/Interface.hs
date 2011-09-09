{-# LANGUAGE TypeFamilies, FlexibleContexts #-}

module Terms.Interface where

class Ord (Var r) => TermRep r where
  type Type r
  type Term r
  type Var r
