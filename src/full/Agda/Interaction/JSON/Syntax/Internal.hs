{-# LANGUAGE OverloadedStrings #-}

-- | Instances of EncodeTCM or ToJSON under Agda.Syntax.Internal

module Agda.Interaction.JSON.Syntax.Internal where

import Data.Aeson

import Agda.Interaction.JSON.Syntax.Abstract
import Agda.Interaction.JSON.Syntax.Common
import Agda.Interaction.JSON.Syntax.Literal
import Agda.Syntax.Internal

--------------------------------------------------------------------------------
-- Agda.Syntax.Internal


instance ToJSON ConHead where
  toJSON (ConHead name ind fields) = object
    [ "name"      .= name
    , "inductive" .= ind
    , "fields"    .= fields
    ]

instance ToJSON Term where
  toJSON (Var n elims) = object
    [ "kind"      .= String "Var"
    , "index"     .= n
    , "elims"     .= elims
    ]
  toJSON (Lam argInfo binder) = object
    [ "kind"      .= String "Lam"
    , "argInfo"   .= argInfo
    , "binder"    .= binder
    ]
  toJSON (Lit lit) = object
    [ "kind"      .= String "Lit"
    , "literal"   .= lit
    ]
  toJSON (Def name elims) = object
    [ "kind"      .= String "Def"
    , "name"      .= name
    , "elims"     .= elims
    ]
  toJSON (Con conHead conInfo elims) = object
    [ "kind"      .= String "Con"
    , "conHead"   .= conHead
    , "conInfo"   .= conInfo
    , "elims"     .= elims
    ]
  toJSON (Pi domain binder) = object
    [ "kind"      .= String "Pi"
    , "domain"    .= domain
    , "binder"    .= binder
    ]
  toJSON (Sort sort) = object
    [ "kind"      .= String "Sort"
    , "sort"      .= sort
    ]
  toJSON (Level level) = object
    [ "kind"      .= String "Level"
    , "level"     .= level
    ]
  toJSON (MetaV metaId elims) = object
    [ "kind"      .= String "MetaV"
    , "metaId"    .= metaId
    , "elims"     .= elims
    ]
  toJSON (DontCare term) = object
    [ "kind"      .= String "DontCare"
    , "term"      .= term
    ]
  toJSON (Dummy s) = object
    [ "kind"        .= String "Dummy"
    , "description" .= s
    ]

instance ToJSON a => ToJSON (Elim' a) where
  toJSON (Apply arg) = object
    [ "kind"      .= String "Apply"
    , "arg"       .= arg
    ]
  toJSON (Proj origin name) = object
    [ "kind"        .= String "Proj"
    , "projOrigin"  .= origin
    , "name"        .= name
    ]
  toJSON (IApply x y r) = object
    [ "kind"      .= String "IApply"
    , "endpoint1" .= x
    , "endpoint2" .= y
    , "endpoint3" .= r
    ]

instance ToJSON a => ToJSON (Abs a) where
  toJSON (Abs name value) = object
    [ "kind"      .= String "Abs"
    , "name"      .= name
    , "value"       .= value
    ]
  toJSON (NoAbs name value) = object
    [ "kind"      .= String "NoAbs"
    , "name"      .= name
    , "value"       .= value
    ]

instance ToJSON a => ToJSON (Type' a) where
  toJSON (El sort value) = object
    [ "sort"    .= sort
    , "value"   .= value
    ]

instance ToJSON a => ToJSON (Tele a) where
  toJSON EmptyTel = object
    [ "kind"      .= String "EmptyTel"
    ]
  toJSON (ExtendTel value binder) = object
    [ "kind"      .= String "ExtendTel"
    , "value"     .= value
    , "binder"    .= binder
    ]

instance ToJSON Sort where
  toJSON (Type level) = object
    [ "kind"      .= String "Type"
    , "level"     .= level
    ]
  toJSON (Prop level) = object
    [ "kind"      .= String "Prop"
    , "level"     .= level
    ]
  toJSON Inf = object
    [ "kind"      .= String "Inf"
    ]
  toJSON SizeUniv = object
    [ "kind"      .= String "SizeUniv"
    ]
  toJSON (PiSort sort binder) = object
    [ "kind"      .= String "PiSort"
    , "sort"      .= sort
    , "binder"    .= binder
    ]
  toJSON (UnivSort sort) = object
    [ "kind"      .= String "UnivSort"
    , "sort"      .= sort
    ]
  toJSON (MetaS metaId elims) = object
    [ "kind"      .= String "MetaS"
    , "metaId"    .= metaId
    , "elims"     .= elims
    ]

instance ToJSON Level where
  toJSON (Max levels) = toJSON levels

instance ToJSON PlusLevel where
  toJSON (ClosedLevel n) = object
    [ "kind"      .= String "ClosedLevel"
    , "level"     .= n
    ]
  toJSON (Plus n levelAtom) = object
    [ "kind"      .= String "Plus"
    , "level"     .= n
    , "levelAtom" .= levelAtom
    ]

instance ToJSON LevelAtom where
  toJSON (MetaLevel metaId elims) = object
    [ "kind"      .= String "MetaLevel"
    , "metaId"    .= metaId
    , "elims"     .= elims
    ]
  toJSON (BlockedLevel metaId term) = object
    [ "kind"      .= String "BlockedLevel"
    , "metaId"    .= metaId
    , "term"      .= term
    ]
  toJSON (NeutralLevel notBlocked term) = object
    [ "kind"        .= String "NeutralLevel"
    , "notBlocked"  .= notBlocked
    , "term"        .= term
    ]
  toJSON (UnreducedLevel term) = object
    [ "kind"      .= String "UnreducedLevel"
    , "term"      .= term
    ]

instance ToJSON NotBlocked where
  toJSON (StuckOn elim) = object
    [ "kind"      .= String "StuckOn"
    , "elim"     .= elim
    ]
  toJSON Underapplied = object
    [ "kind"      .= String "Underapplied"
    ]
  toJSON AbsurdMatch = object
    [ "kind"      .= String "AbsurdMatch"
    ]
  toJSON MissingClauses = object
    [ "kind"      .= String "MissingClauses"
    ]
  toJSON ReallyNotBlocked = object
    [ "kind"      .= String "ReallyNotBlocked"
    ]
