{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE CPP #-}

-- | Contains the state monad for transformations. Basically just exports
-- the CompileT monad and related functions, but only the subset which
-- can be safely used inside transformations.
module Agda.Compiler.UHC.Transform
  ( uhcError

  , Transform
  , TransformT

  , getCoreName
  , getCoreName1
  , getConstrInfo
  , getConstrFun
  , isConstrInstantiated

  , getCurrentModule

  , conArityAndPars
  , replaceAt
  )
where

import Agda.Compiler.UHC.AuxAST as AuxAST
import Agda.Compiler.UHC.CompileState
import Agda.TypeChecking.Monad (TCM)

type TransformT = CompileT

type Transform = AMod -> TransformT TCM AMod

