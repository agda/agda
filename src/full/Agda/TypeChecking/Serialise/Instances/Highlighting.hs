{-# OPTIONS_GHC -fno-warn-orphans #-}

module Agda.TypeChecking.Serialise.Instances.Highlighting where

import qualified Agda.Interaction.Highlighting.Range   as HR
import qualified Agda.Interaction.Highlighting.Precise as HP

import Agda.TypeChecking.Serialise.Base
import Agda.TypeChecking.Serialise.Instances.Common ()

instance EmbPrj HR.Range where
  icod_ (HR.Range a b) = icodeN' HR.Range a b

  value = valueN HR.Range

instance EmbPrj HP.NameKind where
  icod_ HP.Bound           = icodeN' HP.Bound
  icod_ (HP.Constructor a) = icodeN 1 HP.Constructor a
  icod_ HP.Datatype        = icodeN 2 ()
  icod_ HP.Field           = icodeN 3 ()
  icod_ HP.Function        = icodeN 4 ()
  icod_ HP.Module          = icodeN 5 ()
  icod_ HP.Postulate       = icodeN 6 ()
  icod_ HP.Primitive       = icodeN 7 ()
  icod_ HP.Record          = icodeN 8 ()
  icod_ HP.Argument        = icodeN 9 ()
  icod_ HP.Macro           = icodeN 10 ()
  icod_ HP.Generalizable   = icodeN 11 ()

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
    valu [11]    = valuN HP.Generalizable
    valu _       = malformed

instance EmbPrj HP.Aspect where
  icod_ HP.Comment        = icodeN 0 ()
  icod_ HP.Keyword       = icodeN 1 ()
  icod_ HP.String        = icodeN 2 ()
  icod_ HP.Number        = icodeN 3 ()
  icod_ HP.Symbol        = icodeN' HP.Symbol
  icod_ HP.PrimitiveType = icodeN 4 ()
  icod_ (HP.Name mk b)   = icodeN 5 HP.Name mk b
  icod_ HP.Pragma        = icodeN 6 ()
  icod_ HP.Background    = icodeN 7 ()
  icod_ HP.Markup        = icodeN 8 ()

  value = vcase valu where
    valu [0]        = valuN HP.Comment
    valu [1]        = valuN HP.Keyword
    valu [2]        = valuN HP.String
    valu [3]        = valuN HP.Number
    valu []         = valuN HP.Symbol
    valu [4]        = valuN HP.PrimitiveType
    valu [5, mk, b] = valuN HP.Name mk b
    valu [6]        = valuN HP.Pragma
    valu [7]        = valuN HP.Background
    valu [8]        = valuN HP.Markup
    valu _          = malformed

instance EmbPrj HP.OtherAspect where
  icod_ HP.Error               = icodeN 0 ()
  icod_ HP.DottedPattern       = icodeN' HP.DottedPattern
  icod_ HP.UnsolvedMeta        = icodeN 2 ()
  icod_ HP.TerminationProblem  = icodeN 3 ()
  icod_ HP.IncompletePattern   = icodeN 4 ()
  icod_ HP.TypeChecks          = icodeN 5 ()
  icod_ HP.UnsolvedConstraint  = icodeN 6 ()
  icod_ HP.PositivityProblem   = icodeN 7 ()
  icod_ HP.Deadcode            = icodeN 8 ()
  icod_ HP.CoverageProblem     = icodeN 9 ()
  icod_ HP.CatchallClause      = icodeN 10 ()

  value = vcase valu where
    valu [0] = valuN HP.Error
    valu []  = valuN HP.DottedPattern
    valu [2] = valuN HP.UnsolvedMeta
    valu [3] = valuN HP.TerminationProblem
    valu [4] = valuN HP.IncompletePattern
    valu [5] = valuN HP.TypeChecks
    valu [6] = valuN HP.UnsolvedConstraint
    valu [7] = valuN HP.PositivityProblem
    valu [8] = valuN HP.Deadcode
    valu [9] = valuN HP.CoverageProblem
    valu [10] = valuN HP.CatchallClause
    valu _   = malformed

instance EmbPrj HP.Aspects where
  icod_ (HP.Aspects a b c d e) = icodeN' HP.Aspects a b c d e

  value = valueN HP.Aspects

instance EmbPrj HP.DefinitionSite where
  icod_ (HP.DefinitionSite a b c d) = icodeN' HP.DefinitionSite a b c d

  value = valueN HP.DefinitionSite

instance EmbPrj HP.CompressedFile where
  icod_ (HP.CompressedFile f) = icodeN' HP.CompressedFile f

  value = valueN HP.CompressedFile

instance EmbPrj HP.TokenBased where
  icod_ HP.TokenBased        = icodeN 0 ()
  icod_ HP.NotOnlyTokenBased = icodeN' HP.NotOnlyTokenBased

  value = vcase valu where
    valu [0] = valuN HP.TokenBased
    valu []  = valuN HP.NotOnlyTokenBased
    valu _   = malformed
