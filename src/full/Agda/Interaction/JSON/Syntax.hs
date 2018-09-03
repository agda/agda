{-# LANGUAGE OverloadedStrings #-}

-- | Instances of EncodeTCM or ToJSON under Agda.Syntax

module Agda.Interaction.JSON.Syntax where

import Data.Aeson hiding (Result(..))

import Agda.Interaction.JSON.Encoding
import Agda.Interaction.JSON.Utils

import Agda.Syntax.Common
import qualified Agda.Syntax.Abstract     as A
import qualified Agda.Syntax.Concrete     as C
import qualified Agda.Syntax.Fixity       as F
import qualified Agda.Syntax.Internal     as I
import qualified Agda.Syntax.Literal      as L
import qualified Agda.Syntax.Notation     as N
import qualified Agda.Syntax.Position     as P
import qualified Agda.Syntax.Scope.Base   as S

--------------------------------------------------------------------------------
-- Agda.Syntax.Common

instance ToJSON InteractionId where
  toJSON (InteractionId i) = toJSON i

instance ToJSON FreeVariables where
  toJSON UnknownFVs       = Null
  toJSON (KnownFVs vars)  = toJSON vars

instance ToJSON Modality where
  toJSON (Modality relevance quantity) = object
    [ "relevance" .= relevance
    , "quantity"  .= quantity
    ]

instance ToJSON Quantity where
  toJSON Quantity0  = String "Quantity0"
  toJSON Quantityω  = String "QuantityOmega"

instance ToJSON Relevance where
  toJSON Relevant   = String "Relevant"
  toJSON NonStrict  = String "NonStrict"
  toJSON Irrelevant = String "Irrelevant"

instance ToJSON Overlappable where
  toJSON YesOverlap = String "YesOverlap"
  toJSON NoOverlap  = String "NoOverlap"

instance ToJSON Hiding where
  toJSON Hidden     = object [ "kind" .= String "Hidden" ]
  toJSON NotHidden  = object [ "kind" .= String "NotHidden" ]
  toJSON (Instance overlappable) = object
    [ "kind"          .= String "Instance"
    , "overlappable"  .= overlappable
    ]

instance ToJSON Origin where
  toJSON UserWritten  = String "UserWritten"
  toJSON Inserted     = String "Inserted"
  toJSON Reflected    = String "Reflected"
  toJSON CaseSplit    = String "CaseSplit"
  toJSON Substitution = String "Substitution"

instance ToJSON ArgInfo where
  toJSON (ArgInfo hiding modality origin freeVars) = object
    [ "hiding"    .= hiding
    , "modality"  .= modality
    , "origin"    .= origin
    , "freeVars"  .= freeVars
    ]

instance ToJSON NameId where
  toJSON (NameId name modul) = object
    [ "name"    .= name
    , "module"  .= modul
    ]

instance ToJSON a => ToJSON (Ranged a) where
  toJSON (Ranged range value) = object
    [ "range"   .= range
    , "value"   .= value
    ]

instance (ToJSON name, ToJSON a) => ToJSON (Named name a) where
  toJSON (Named name value) = object
    [ "name"    .= name
    , "value"   .= value
    ]

instance ToJSON a => ToJSON (Arg a) where
  toJSON (Arg argInfo value) = object
    [ "argInfo" .= argInfo
    , "value"   .= value
    ]

instance ToJSON a => ToJSON (Dom a) where
  toJSON (Dom argInfo finite value) = object
    [ "argInfo" .= argInfo
    , "finite"  .= finite
    , "value"   .= value
    ]

instance ToJSON DataOrRecord where
  toJSON IsData   = String "IsData"
  toJSON IsRecord = String "IsRecord"

instance ToJSON ProjOrigin where
  toJSON ProjPrefix   = String "ProjPrefix"
  toJSON ProjPostfix  = String "ProjPostfix"
  toJSON ProjSystem   = String "ProjSystem"

instance ToJSON MetaId where
  toJSON (MetaId i)   = toJSON i

instance ToJSON Induction where
  toJSON Inductive   = String "Inductive"
  toJSON CoInductive = String "CoInductive"

instance ToJSON ConOrigin where
  toJSON ConOSystem = String "ConOSystem"
  toJSON ConOCon    = String "ConOCon"
  toJSON ConORec    = String "ConORec"
  toJSON ConOSplit  = String "ConOSplit"

--------------------------------------------------------------------------------
-- Agda.Syntax.Abstract

instance ToJSON A.Name where
  toJSON (A.Name name concrete bindingSite fixity) = object
    [ "id"          .= name
    , "concrete"    .= concrete
    , "bindingSite" .= bindingSite
    , "fixity"      .= fixity
    ]

instance ToJSONKey A.QName
instance ToJSON A.QName where
  toJSON (A.QName moduleName name) = object
    [ "module"  .= moduleName
    , "name"    .= name
    ]

instance ToJSONKey A.ModuleName where
instance ToJSON A.ModuleName where
  toJSON (A.MName names) = toJSON names

--------------------------------------------------------------------------------
-- Agda.Syntax.Concrete

instance ToJSON C.NamePart where
  toJSON C.Hole      = Null
  toJSON (C.Id name) = toJSON name

instance ToJSON C.Name where
  toJSON (C.Name   range parts) = object
    [ "kind"  .= String "Name"
    , "range" .= range
    , "parts" .= parts
    ]
  toJSON (C.NoName range name) = object
    [ "kind"  .= String "NoName"
    , "range" .= range
    , "name"  .= name
    ]

instance ToJSON C.QName where
  toJSON = toJSON . toList
    where
      toList (C.QName name)      = name : []
      toList (C.Qual name qname) = name : toList qname

--------------------------------------------------------------------------------
-- Agda.Syntax.Fixity

instance ToJSON F.NotationSection where
  toJSON (F.NotationSection notation kind level isSection) = object
    [ "kind"      .= kind
    , "notation"  .= notation
    , "level"     .= level
    , "isSection" .= isSection
    ]

instance ToJSON F.NewNotation where
  toJSON (F.NewNotation name names fixity notation isOperator) = object
    [ "name"        .= name
    , "names"       .= names
    , "fixity"      .= fixity
    , "notation"    .= notation
    , "isOperator"  .= isOperator
    ]

instance ToJSON F.PrecedenceLevel where
  toJSON F.Unrelated = Null
  toJSON (F.Related n) = toJSON n

instance ToJSON F.Associativity where
  toJSON F.NonAssoc = String "NonAssoc"
  toJSON F.LeftAssoc = String "LeftAssoc"
  toJSON F.RightAssoc = String "RightAssoc"

instance ToJSON F.Fixity where
  toJSON (F.Fixity range level assoc) = object
    [ "range" .= range
    , "level" .= level
    , "assoc" .= assoc
    ]

instance ToJSON F.Fixity' where
  toJSON (F.Fixity' fixity notation range) = object
    [ "fixity"    .= fixity
    , "notation"  .= notation
    , "range"     .= range
    ]

--------------------------------------------------------------------------------
-- Agda.Syntax.Internal

instance ToJSON I.Term where
  toJSON (I.Var n elims) = object
    [ "kind"      .= String "Var"
    , "index"     .= n
    , "elims"     .= elims
    ]
  toJSON (I.Lam argInfo binder) = object
    [ "kind"      .= String "Lam"
    , "argInfo"   .= argInfo
    , "binder"    .= binder
    ]
  toJSON (I.Lit lit) = object
    [ "kind"      .= String "Lit"
    , "literal"   .= lit
    ]
  toJSON (I.Def name elims) = object
    [ "kind"      .= String "Def"
    , "name"      .= name
    , "elims"     .= elims
    ]
  toJSON (I.Con conHead conInfo elims) = object
    [ "kind"      .= String "Con"
    , "conHead"   .= conHead
    , "conInfo"   .= conInfo
    , "elims"     .= elims
    ]
  toJSON (I.Pi domain binder) = object
    [ "kind"      .= String "Pi"
    , "domain"    .= domain
    , "binder"    .= binder
    ]
  toJSON (I.Sort sort) = object
    [ "kind"      .= String "Sort"
    , "sort"      .= sort
    ]
  toJSON (I.Level level) = object
    [ "kind"      .= String "Level"
    , "level"     .= level
    ]
  toJSON (I.MetaV metaId elims) = object
    [ "kind"      .= String "MetaV"
    , "metaId"    .= metaId
    , "elims"     .= elims
    ]
  toJSON (I.DontCare term) = object
    [ "kind"      .= String "DontCare"
    , "term"      .= term
    ]
  toJSON (I.Dummy s) = object
    [ "kind"        .= String "Dummy"
    , "description" .= s
    ]

instance ToJSON a => ToJSON (I.Type' a) where
  toJSON (I.El sort value) = object
    [ "sort"    .= sort
    , "value"   .= value
    ]

instance ToJSON I.Sort where
  toJSON (I.Type level) = object
    [ "kind"      .= String "Type"
    , "level"     .= level
    ]
  toJSON (I.Prop level) = object
    [ "kind"      .= String "Prop"
    , "level"     .= level
    ]
  toJSON I.Inf = object
    [ "kind"      .= String "Inf"
    ]
  toJSON I.SizeUniv = object
    [ "kind"      .= String "SizeUniv"
    ]
  toJSON (I.PiSort sort binder) = object
    [ "kind"      .= String "PiSort"
    , "sort"      .= sort
    , "binder"    .= binder
    ]
  toJSON (I.UnivSort sort) = object
    [ "kind"      .= String "UnivSort"
    , "sort"      .= sort
    ]
  toJSON (I.MetaS metaId elims) = object
    [ "kind"      .= String "MetaS"
    , "metaId"    .= metaId
    , "elims"     .= elims
    ]

instance ToJSON I.Level where
  toJSON (I.Max levels) = toJSON levels

instance ToJSON I.PlusLevel where
  toJSON (I.ClosedLevel n) = object
    [ "kind"      .= String "ClosedLevel"
    , "level"     .= n
    ]
  toJSON (I.Plus n levelAtom) = object
    [ "kind"      .= String "Plus"
    , "level"     .= n
    , "levelAtom" .= levelAtom
    ]

instance ToJSON I.LevelAtom where
  toJSON (I.MetaLevel metaId elims) = object
    [ "kind"      .= String "MetaLevel"
    , "metaId"    .= metaId
    , "elims"     .= elims
    ]
  toJSON (I.BlockedLevel metaId term) = object
    [ "kind"      .= String "BlockedLevel"
    , "metaId"    .= metaId
    , "term"      .= term
    ]
  toJSON (I.NeutralLevel notBlocked term) = object
    [ "kind"        .= String "NeutralLevel"
    , "notBlocked"  .= notBlocked
    , "term"        .= term
    ]
  toJSON (I.UnreducedLevel term) = object
    [ "kind"      .= String "UnreducedLevel"
    , "term"      .= term
    ]

instance ToJSON I.NotBlocked where
  toJSON (I.StuckOn elim) = object
    [ "kind"      .= String "StuckOn"
    , "elim"     .= elim
    ]
  toJSON I.Underapplied = object
    [ "kind"      .= String "Underapplied"
    ]
  toJSON I.AbsurdMatch = object
    [ "kind"      .= String "AbsurdMatch"
    ]
  toJSON I.MissingClauses = object
    [ "kind"      .= String "MissingClauses"
    ]
  toJSON I.ReallyNotBlocked = object
    [ "kind"      .= String "ReallyNotBlocked"
    ]

instance ToJSON a => ToJSON (I.Elim' a) where
  toJSON (I.Apply arg) = object
    [ "kind"      .= String "Apply"
    , "arg"       .= arg
    ]
  toJSON (I.Proj origin name) = object
    [ "kind"        .= String "Proj"
    , "projOrigin"  .= origin
    , "name"        .= name
    ]
  toJSON (I.IApply x y r) = object
    [ "kind"      .= String "IApply"
    , "endpoint1" .= x
    , "endpoint2" .= y
    , "endpoint3" .= r
    ]

instance ToJSON a => ToJSON (I.Abs a) where
  toJSON (I.Abs name value) = object
    [ "kind"      .= String "Abs"
    , "name"      .= name
    , "value"       .= value
    ]
  toJSON (I.NoAbs name value) = object
    [ "kind"      .= String "NoAbs"
    , "name"      .= name
    , "value"       .= value
    ]

instance ToJSON I.ConHead where
  toJSON (I.ConHead name ind fields) = object
    [ "name"      .= name
    , "inductive" .= ind
    , "fields"    .= fields
    ]

instance ToJSON a => ToJSON (I.Tele a) where
  toJSON I.EmptyTel = object
    [ "kind"      .= String "EmptyTel"
    ]
  toJSON (I.ExtendTel value binder) = object
    [ "kind"      .= String "ExtendTel"
    , "value"     .= value
    , "binder"    .= binder
    ]

--------------------------------------------------------------------------------
-- Agda.Syntax.Literal

instance ToJSON L.Literal where
  toJSON (L.LitNat range value) = object
    [ "kind"      .= String "LitNat"
    , "range"     .= range
    , "value"     .= value
    ]
  toJSON (L.LitWord64 range value) = object
    [ "kind"      .= String "LitWord64"
    , "range"     .= range
    , "value"     .= value
    ]
  toJSON (L.LitFloat range value) = object
    [ "kind"      .= String "LitFloat"
    , "range"     .= range
    , "value"     .= value
    ]
  toJSON (L.LitString range value) = object
    [ "kind"      .= String "LitString"
    , "range"     .= range
    , "value"     .= value
    ]
  toJSON (L.LitChar range value) = object
    [ "kind"      .= String "LitChar"
    , "range"     .= range
    , "value"     .= value
    ]
  toJSON (L.LitQName range value) = object
    [ "kind"      .= String "LitQName"
    , "range"     .= range
    , "value"     .= value
    ]
  toJSON (L.LitMeta range path metaId) = object
    [ "kind"      .= String "LitMeta"
    , "range"     .= range
    , "path"      .= path
    , "metaId"    .= metaId
    ]


--------------------------------------------------------------------------------
-- Agda.Syntax.Notation

instance ToJSON N.GenPart where
  toJSON (N.BindHole n) = object
    [ "kind"      .= String "BindHole"
    , "position"  .= n
    ]
  toJSON (N.NormalHole n) = object
    [ "kind"      .= String "NormalHole"
    , "position"  .= n
    ]
  toJSON (N.WildHole n) = object
    [ "kind"      .= String "WildHole"
    , "position"  .= n
    ]
  toJSON (N.IdPart name) = object
    [ "kind"      .= String "IdPart"
    , "rawName"   .= name
    ]

instance ToJSON N.NotationKind where
  toJSON N.InfixNotation    = String "InfixNotation"
  toJSON N.PrefixNotation   = String "PrefixNotation"
  toJSON N.PostfixNotation  = String "PostfixNotation"
  toJSON N.NonfixNotation   = String "NonfixNotation"
  toJSON N.NoNotation       = String "NoNotation"

--------------------------------------------------------------------------------
-- Agda.Syntax.Position
instance ToJSON a => ToJSON (P.Position' a) where
  toJSON (P.Pn _ pos line col) = toJSON
    [ toJSON line, toJSON col, toJSON pos ]

instance ToJSON a => ToJSON (P.Interval' a) where
  toJSON (P.Interval start end) = object
    [ "start" .= start
    , "end"   .= end
    ]

instance ToJSON a => ToJSON (P.Range' a) where
  toJSON (P.Range src is) = object
    [ "intervals" .= is
    , "source" .= src
    ]
  toJSON P.NoRange = object
    [ "intervals" .= ([] :: [P.Interval' a])
    ]
