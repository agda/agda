{-# OPTIONS_GHC -Wunused-imports #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Agda.TypeChecking.Serialise.Instances.Highlighting where

import qualified Data.Map.Strict as Map
import Data.Strict.Tuple (Pair(..))

import qualified Agda.Interaction.Highlighting.Range   as HR
import qualified Agda.Interaction.Highlighting.Precise as HP
import qualified Agda.Utils.RangeMap                   as RM

import Agda.TypeChecking.Serialise.Base
import Agda.TypeChecking.Serialise.Instances.Common () --instance only

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
  icod_ HP.Hole          = icodeN 9 ()

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
    valu [9]        = valuN HP.Hole
    valu _          = malformed

instance EmbPrj HP.OtherAspect where
  icod_ HP.Error                = pure 0
  icod_ HP.ErrorWarning         = pure 1
  icod_ HP.DottedPattern        = pure 2
  icod_ HP.UnsolvedMeta         = pure 3
  icod_ HP.TerminationProblem   = pure 4
  icod_ HP.IncompletePattern    = pure 5
  icod_ HP.TypeChecks           = pure 6
  icod_ HP.UnsolvedConstraint   = pure 7
  icod_ HP.PositivityProblem    = pure 8
  icod_ HP.Deadcode             = pure 9
  icod_ HP.CoverageProblem      = pure 10
  icod_ HP.CatchallClause       = pure 11
  icod_ HP.ConfluenceProblem    = pure 12
  icod_ HP.MissingDefinition    = pure 13
  icod_ HP.ShadowingInTelescope = pure 14

  value = \case
    0  -> pure HP.Error
    1  -> pure HP.ErrorWarning
    2  -> pure HP.DottedPattern
    3  -> pure HP.UnsolvedMeta
    4  -> pure HP.TerminationProblem
    5  -> pure HP.IncompletePattern
    6  -> pure HP.TypeChecks
    7  -> pure HP.UnsolvedConstraint
    8  -> pure HP.PositivityProblem
    9  -> pure HP.Deadcode
    10 -> pure HP.CoverageProblem
    11 -> pure HP.CatchallClause
    12 -> pure HP.ConfluenceProblem
    13 -> pure HP.MissingDefinition
    14 -> pure HP.ShadowingInTelescope
    _  -> malformed

instance EmbPrj HP.Aspects where
  icod_ (HP.Aspects a b c d e) = icodeN' HP.Aspects a b c d e

  value = valueN HP.Aspects

instance EmbPrj HP.DefinitionSite where
  icod_ (HP.DefinitionSite a b c d) = icodeN' HP.DefinitionSite a b c d

  value = valueN HP.DefinitionSite

instance EmbPrj a => EmbPrj (RM.RangeMap a) where
  -- Write the RangeMap as flat list rather than a list of (Int, (Int, x)). Much
  -- like Map, we need to call `convert' in the tail position and so the output
  -- list is written (and read) in reverse order.
  icod_ (RM.RangeMap f) = icodeNode =<< convert [] (Map.toAscList f) where
    convert ys [] = return ys
    convert ys ((start, RM.PairInt (end :!: entry)):xs) = do
      start <- icode start
      end <- icode end
      entry <- icode entry
      convert (start:end:entry:ys) xs

  value = vcase (fmap (RM.RangeMap . Map.fromDistinctAscList) . convert []) where
    convert ys [] = return ys
    convert ys (start:end:entry:xs) = do
      start <- value start
      end <- value end
      entry <- value entry
      convert ((start, RM.PairInt (end :!: entry)):ys) xs
    convert _ _ = malformed

instance EmbPrj HP.TokenBased where
  icod_ HP.TokenBased        = pure 0
  icod_ HP.NotOnlyTokenBased = pure 1

  value = \case
    0 -> pure HP.TokenBased
    1 -> pure HP.NotOnlyTokenBased
    _ -> malformed
