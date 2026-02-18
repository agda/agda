
{-# OPTIONS_GHC -Wunused-imports #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Agda.TypeChecking.Serialise.Instances.Highlighting where

import Control.Monad.Reader
import qualified Data.Map.Strict as Map

import Agda.Utils.Monad
import Agda.Utils.Range (Range(..))
import qualified Agda.Interaction.Highlighting.Precise as HP
import Agda.Utils.RangeMap (PairInt(..))
import qualified Agda.Utils.RangeMap as RM

import Agda.TypeChecking.Serialise.Base
import Agda.TypeChecking.Serialise.Instances.Common () --instance only

instance EmbPrj Range where
  icod_ (Range a b) = icodeN' Range a b

  value = valueN Range

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
    valu N0       = valuN HP.Bound
    valu (N2 1 a) = valuN HP.Constructor a
    valu (N1 2)   = valuN HP.Datatype
    valu (N1 3)   = valuN HP.Field
    valu (N1 4)   = valuN HP.Function
    valu (N1 5)   = valuN HP.Module
    valu (N1 6)   = valuN HP.Postulate
    valu (N1 7)   = valuN HP.Primitive
    valu (N1 8)   = valuN HP.Record
    valu (N1 9)   = valuN HP.Argument
    valu (N1 10)  = valuN HP.Macro
    valu (N1 11)  = valuN HP.Generalizable
    valu _        = malformed

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
  icod_ (HP.URL a)       = icodeN 10 HP.URL a

  value = vcase valu where
    valu (N1 0)      = valuN HP.Comment
    valu (N1 1)      = valuN HP.Keyword
    valu (N1 2)      = valuN HP.String
    valu (N1 3)      = valuN HP.Number
    valu N0          = valuN HP.Symbol
    valu (N1 4)      = valuN HP.PrimitiveType
    valu (N3 5 mk b) = valuN HP.Name mk b
    valu (N1 6)      = valuN HP.Pragma
    valu (N1 7)      = valuN HP.Background
    valu (N1 8)      = valuN HP.Markup
    valu (N1 9)      = valuN HP.Hole
    valu (N2 10 a)   = valuN HP.URL a
    valu _           = malformed

instance EmbPrj HP.OtherAspect where
  icod_ HP.Error                = pure 0
  icod_ HP.ErrorWarning         = pure 1
  icod_ HP.DottedPattern        = pure 2
  icod_ HP.UnsolvedMeta         = pure 3
  icod_ HP.TerminationProblem   = pure 4
  -- 5 is unused
  icod_ HP.TypeChecks           = pure 6
  icod_ HP.UnsolvedConstraint   = pure 7
  icod_ HP.PositivityProblem    = pure 8
  icod_ HP.Deadcode             = pure 9
  icod_ HP.CoverageProblem      = pure 10
  icod_ HP.CatchallClause       = pure 11
  icod_ HP.ConfluenceProblem    = pure 12
  icod_ HP.MissingDefinition    = pure 13
  icod_ HP.ShadowingInTelescope = pure 14
  icod_ HP.CosmeticProblem      = pure 15
  icod_ HP.InstanceProblem      = pure 16

  value = \case
    0  -> pure HP.Error
    1  -> pure HP.ErrorWarning
    2  -> pure HP.DottedPattern
    3  -> pure HP.UnsolvedMeta
    4  -> pure HP.TerminationProblem
    -- 5 is unused
    6  -> pure HP.TypeChecks
    7  -> pure HP.UnsolvedConstraint
    8  -> pure HP.PositivityProblem
    9  -> pure HP.Deadcode
    10 -> pure HP.CoverageProblem
    11 -> pure HP.CatchallClause
    12 -> pure HP.ConfluenceProblem
    13 -> pure HP.MissingDefinition
    14 -> pure HP.ShadowingInTelescope
    15 -> pure HP.CosmeticProblem
    16 -> pure HP.InstanceProblem
    _  -> malformed

instance EmbPrj HP.Aspects where
  icod_ (HP.Aspects a b c d e) = icodeN' HP.Aspects a b c d e

  value = valueN HP.Aspects

instance EmbPrj HP.DefinitionSite where
  icod_ (HP.DefinitionSite a b c d) = icodeN' HP.DefinitionSite a b c d

  value = valueN HP.DefinitionSite

data KVS a = Cons !Int !Int a !(KVS a) | Nil

toAscList' :: RM.RangeMap a -> KVS a
toAscList' (RM.RangeMap x) =
  Map.foldrWithKey'
    (\a (b :!: c) !acc -> Cons a b c acc)
    Nil x

{-# INLINABLE icodRM #-}
icodRM :: EmbPrj a => KVS a -> S Node
icodRM xs = ReaderT \r -> case xs of
  Nil ->
    pure N0
  Cons a b c Nil -> flip runReaderT r $
    N3 <$!> icode a <*!> icode b <*!> icode c
  Cons a b c (Cons d e f xs) -> flip runReaderT r $
    N6 <$!> icode a <*!> icode b <*!> icode c
       <*!> icode d <*!> icode e <*!> icode f <*!> icodRM xs

{-# INLINABLE valueRM #-}
valueRM :: EmbPrj a => Node -> R [(Int, PairInt a)]
valueRM as = ReaderT \r -> case as of
  N0 ->
    pure []
  N3 a b c -> flip runReaderT r do
    !a <- value a
    !b <- value b
    !c <- value c
    pure [(a, b :!: c)]
  N6 a b c d e f as -> flip runReaderT r do
    !a  <- value a
    !b  <- value b
    !c  <- value c
    !d  <- value d
    !e  <- value e
    !f  <- value f
    !as <- valueRM as
    pure ((a, b :!: c):(d, e :!: f):as)
  _ -> malformedIO

-- We serialize as a flat list of triples
instance EmbPrj a => EmbPrj (RM.RangeMap a) where
  {-# INLINE icod_ #-}
  icod_ x = icodeNode =<< icodRM (toAscList' x) where
  {-# INLINE value #-}
  value = vcase (\n -> RM.RangeMap . Map.fromDistinctAscList <$!> valueRM n) where

instance EmbPrj HP.TokenBased where
  icod_ HP.TokenBased        = pure 0
  icod_ HP.NotOnlyTokenBased = pure 1

  value = \case
    0 -> pure HP.TokenBased
    1 -> pure HP.NotOnlyTokenBased
    _ -> malformed
