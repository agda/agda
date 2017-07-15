{-# OPTIONS --warning=error #-}

module AbstractModuleMacro where

import Common.Issue481ParametrizedModule as P

abstract
  module M = P Set
