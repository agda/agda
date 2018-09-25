{-# LANGUAGE OverloadedStrings #-}

-- | Instances of EncodeTCM or ToJSON under Agda.Syntax.Internal

module Agda.Interaction.JSON.Syntax.Internal where

import Data.Aeson

import Agda.Interaction.JSON.Encode
import Agda.Interaction.JSON.Syntax.Abstract.Name
import Agda.Interaction.JSON.Syntax.Common
import Agda.Interaction.JSON.Syntax.Concrete
import Agda.Interaction.JSON.Syntax.Literal
import Agda.Syntax.Internal
import qualified Agda.Syntax.Translation.InternalToAbstract as I2A
import qualified Agda.Syntax.Translation.AbstractToConcrete as A2C

--------------------------------------------------------------------------------
-- Agda.Syntax.Internal


instance ToJSON ConHead where
  toJSON (ConHead name ind fields) = object
    [ "name"      .= name
    , "inductive" .= ind
    , "fields"    .= fields
    ]

instance EncodeTCM Term where
  encodeTCM = I2A.reify >=> A2C.abstractToConcrete_ >=> encodeTCM

instance ToJSON Term where
  toJSON (Var n elims) = kind' "Var"
    [ "index"     .= n
    , "elims"     .= elims
    ]
  toJSON (Lam argInfo binder) = kind' "Lam"
    [ "argInfo"   .= argInfo
    , "binder"    .= binder
    ]
  toJSON (Lit lit) = kind' "Lit"
    [ "literal"   .= lit
    ]
  toJSON (Def name elims) = kind' "Def"
    [ "name"      .= name
    , "elims"     .= elims
    ]
  toJSON (Con conHead conInfo elims) = kind' "Con"
    [ "conHead"   .= conHead
    , "conInfo"   .= conInfo
    , "elims"     .= elims
    ]
  toJSON (Pi domain binder) = kind' "Pi"
    [ "domain"    .= domain
    , "binder"    .= binder
    ]
  toJSON (Sort sort) = kind' "Sort"
    [ "sort"      .= sort
    ]
  toJSON (Level level) = kind' "Level"
    [ "level"     .= level
    ]
  toJSON (MetaV metaId elims) = kind' "MetaV"
    [ "metaId"    .= metaId
    , "elims"     .= elims
    ]
  toJSON (DontCare term) = kind' "DontCare"
    [ "term"      .= term
    ]
  toJSON (Dummy s) = kind' "Dummy"
    [ "description" .= s
    ]

instance EncodeTCM a => EncodeTCM (Elim' a) where
  encodeTCM (Apply arg) = kind "Apply"
    [ "arg"         @= arg
    ]
  encodeTCM (Proj origin name) = kind "Proj"
    [ "projOrigin"  @= origin
    , "name"        @= name
    ]
  encodeTCM (IApply x y r) = kind "IApply"
    [ "endpoint1"   @= x
    , "endpoint2"   @= y
    , "endpoint3"   @= r
    ]
instance ToJSON a => ToJSON (Elim' a) where
  toJSON (Apply arg) = kind' "Apply"
    [ "arg"         .= arg
    ]
  toJSON (Proj origin name) = kind' "Proj"
    [ "projOrigin"  .= origin
    , "name"        .= name
    ]
  toJSON (IApply x y r) = kind' "IApply"
    [ "endpoint1"   .= x
    , "endpoint2"   .= y
    , "endpoint3"   .= r
    ]

instance EncodeTCM a => EncodeTCM (Abs a) where
  encodeTCM (Abs name value) = kind "Abs"
    [ "name"        @= name
    , "value"       @= value
    ]
  encodeTCM (NoAbs name value) = kind "NoAbs"
    [ "name"        @= name
    , "value"       @= value
    ]
instance ToJSON a => ToJSON (Abs a) where
  toJSON (Abs name value) = kind' "Abs"
    [ "name"        .= name
    , "value"       .= value
    ]
  toJSON (NoAbs name value) = kind' "NoAbs"
    [ "name"        .= name
    , "value"       .= value
    ]

instance EncodeTCM Type where
  encodeTCM = I2A.reify >=> A2C.abstractToConcrete_ >=> encodeTCM

instance ToJSON Type where
  toJSON (El sort value) = object
    [ "sort"    .= sort
    , "value"   .= value
    ]

instance EncodeTCM Telescope where
  encodeTCM = I2A.reify >=> A2C.abstractToConcrete_ >=> encodeTCM

instance ToJSON a => ToJSON (Tele a) where
  toJSON EmptyTel = kind' "EmptyTel" []
  toJSON (ExtendTel value binder) = kind' "ExtendTel"
    [ "value"     .= value
    , "binder"    .= binder
    ]

instance EncodeTCM Sort where
  encodeTCM = I2A.reify >=> A2C.abstractToConcrete_ >=> encodeTCM

instance ToJSON Sort where
  toJSON (Type level) = kind' "Type"
    [ "level"     .= level
    ]
  toJSON (Prop level) = kind' "Prop"
    [ "level"     .= level
    ]
  toJSON Inf = kind' "Inf" []
  toJSON SizeUniv = kind' "SizeUniv" []
  toJSON (PiSort sort binder) = kind' "PiSort"
    [ "sort"      .= sort
    , "binder"    .= binder
    ]
  toJSON (UnivSort sort) = kind' "UnivSort"
    [ "sort"      .= sort
    ]
  toJSON (MetaS metaId elims) = kind' "MetaS"
    [ "metaId"    .= metaId
    , "elims"     .= elims
    ]
  toJSON (DummyS description) = kind' "DummyS"
    [ "description" .= description
    ]


instance EncodeTCM Level where
  encodeTCM = I2A.reify >=> A2C.abstractToConcrete_ >=> encodeTCM
instance ToJSON Level where
  toJSON (Max levels) = toJSON levels

instance ToJSON PlusLevel where
  toJSON (ClosedLevel n) = kind' "ClosedLevel"
    [ "level"     .= n
    ]
  toJSON (Plus n levelAtom) = kind' "Plus"
    [ "level"     .= n
    , "levelAtom" .= levelAtom
    ]

instance ToJSON LevelAtom where
  toJSON (MetaLevel metaId elims) = kind' "MetaLevel"
    [ "metaId"    .= metaId
    , "elims"     .= elims
    ]
  toJSON (BlockedLevel metaId term) = kind' "BlockedLevel"
    [ "metaId"    .= metaId
    , "term"      .= term
    ]
  toJSON (NeutralLevel notBlocked term) = kind' "NeutralLevel"
    [ "notBlocked".= notBlocked
    , "term"      .= term
    ]
  toJSON (UnreducedLevel term) = kind' "UnreducedLevel"
    [ "term"      .= term
    ]

instance ToJSON NotBlocked where
  toJSON (StuckOn elim)   = kind' "StuckOn"
    [ "elim"     .= elim
    ]
  toJSON Underapplied     = kind' "Underapplied"      []
  toJSON AbsurdMatch      = kind' "AbsurdMatch"       []
  toJSON MissingClauses   = kind' "MissingClauses"    []
  toJSON ReallyNotBlocked = kind' "ReallyNotBlocked"  []
