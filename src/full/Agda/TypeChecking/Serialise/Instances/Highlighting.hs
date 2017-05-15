{-# OPTIONS_GHC -fno-warn-orphans #-}

module Agda.TypeChecking.Serialise.Instances.Highlighting where

import qualified Agda.Interaction.Highlighting.Range   as HR
import qualified Agda.Interaction.Highlighting.Precise as HP

import Agda.TypeChecking.Serialise.Base
import Agda.TypeChecking.Serialise.Instances.Common ()

instance EmbPrj HR.Range where
  icod_ (HR.Range a b) = icode2' a b

  value = value2 HR.Range

instance EmbPrj HP.NameKind where
  icod_ HP.Bound           = icode0'
  icod_ (HP.Constructor a) = icode1 1 a
  icod_ HP.Datatype        = icode0 2
  icod_ HP.Field           = icode0 3
  icod_ HP.Function        = icode0 4
  icod_ HP.Module          = icode0 5
  icod_ HP.Postulate       = icode0 6
  icod_ HP.Primitive       = icode0 7
  icod_ HP.Record          = icode0 8
  icod_ HP.Argument        = icode0 9
  icod_ HP.Macro           = icode0 10

  value = vcase valu where
    valu []      = valuN HP.Bound
    valu [1 , a] = valuN HP.Constructor a
    valu [2]     = valuN HP.Datatype
    valu [3]     = valuN HP.Field
    valu [4]     = valuN HP.Function
    valu [5]     = valuN HP.Module
    valu [6]     = valuN HP.Postulate
    valu [7]     = valuN HP.Primitive
    valu [8]     = valuN HP.Record
    valu [9]     = valuN HP.Argument
    valu [10]    = valuN HP.Macro
    valu _       = malformed

instance EmbPrj HP.Aspect where
  icod_ HP.Comment       = icode0 0
  icod_ HP.Option        = icode0 1
  icod_ HP.Keyword       = icode0 2
  icod_ HP.String        = icode0 3
  icod_ HP.Number        = icode0 4
  icod_ HP.Symbol        = icode0'
  icod_ HP.PrimitiveType = icode0 6
  icod_ (HP.Name mk b)   = icode2 7 mk b

  value = vcase valu where
    valu [0]        = valuN HP.Comment
    valu [1]        = valuN HP.Option
    valu [2]        = valuN HP.Keyword
    valu [3]        = valuN HP.String
    valu [4]        = valuN HP.Number
    valu []         = valuN HP.Symbol
    valu [6]        = valuN HP.PrimitiveType
    valu [7, mk, b] = valuN HP.Name mk b
    valu _          = malformed

instance EmbPrj HP.OtherAspect where
  icod_ HP.Error               = icode0 0
  icod_ HP.DottedPattern       = icode0'
  icod_ HP.UnsolvedMeta        = icode0 2
  icod_ HP.TerminationProblem  = icode0 3
  icod_ HP.IncompletePattern   = icode0 4
  icod_ HP.TypeChecks          = icode0 5
  icod_ HP.UnsolvedConstraint  = icode0 6
  icod_ HP.PositivityProblem   = icode0 7
  icod_ HP.ReachabilityProblem = icode0 8
  icod_ HP.CoverageProblem     = icode0 9
  icod_ HP.CatchallClause      = icode0 10

  value = vcase valu where
    valu [0] = valuN HP.Error
    valu []  = valuN HP.DottedPattern
    valu [2] = valuN HP.UnsolvedMeta
    valu [3] = valuN HP.TerminationProblem
    valu [4] = valuN HP.IncompletePattern
    valu [5] = valuN HP.TypeChecks
    valu [6] = valuN HP.UnsolvedConstraint
    valu [7] = valuN HP.PositivityProblem
    valu [8] = valuN HP.ReachabilityProblem
    valu [9] = valuN HP.CoverageProblem
    valu [10] = valuN HP.CatchallClause
    valu _   = malformed

instance EmbPrj HP.Aspects where
  icod_ (HP.Aspects a b c d) = icode4' a b c d

  value = value4 HP.Aspects

instance EmbPrj HP.CompressedFile where
  icod_ (HP.CompressedFile f) = icode1' f

  value = value1 HP.CompressedFile
