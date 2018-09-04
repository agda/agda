{-# LANGUAGE OverloadedStrings #-}

-- | Instances of EncodeTCM or ToJSON under Agda.Syntax

module Agda.Interaction.JSON.Syntax where

import Data.Aeson hiding (Result(..))

import Agda.Interaction.JSON.Encoding
import Agda.Interaction.JSON.Utils

import Agda.Interaction.JSON.TypeChecking.Positivity

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

instance ToJSON HasEta where
  toJSON NoEta  = String "NoEta"
  toJSON YesEta = String "YesEta"

instance ToJSON Induction where
  toJSON Inductive   = String "Inductive"
  toJSON CoInductive = String "CoInductive"

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

instance ToJSON a => ToJSON (WithHiding a) where
  toJSON (WithHiding hiding value) = object
    [ "hiding"  .= hiding
    , "value"   .= value
    ]

instance ToJSON Origin where
  toJSON UserWritten  = String "UserWritten"
  toJSON Inserted     = String "Inserted"
  toJSON Reflected    = String "Reflected"
  toJSON CaseSplit    = String "CaseSplit"
  toJSON Substitution = String "Substitution"

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

instance ToJSON FreeVariables where
  toJSON UnknownFVs       = Null
  toJSON (KnownFVs vars)  = toJSON vars

instance ToJSON ArgInfo where
  toJSON (ArgInfo hiding modality origin freeVars) = object
    [ "hiding"    .= hiding
    , "modality"  .= modality
    , "origin"    .= origin
    , "freeVars"  .= freeVars
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

instance (ToJSON name, ToJSON a) => ToJSON (Named name a) where
  toJSON (Named name value) = object
    [ "name"    .= name
    , "value"   .= value
    ]

instance ToJSON a => ToJSON (Ranged a) where
  toJSON (Ranged range value) = object
    [ "range"   .= range
    , "value"   .= value
    ]

instance ToJSON ConOrigin where
  toJSON ConOSystem = String "ConOSystem"
  toJSON ConOCon    = String "ConOCon"
  toJSON ConORec    = String "ConORec"
  toJSON ConOSplit  = String "ConOSplit"

instance ToJSON ProjOrigin where
  toJSON ProjPrefix   = String "ProjPrefix"
  toJSON ProjPostfix  = String "ProjPostfix"
  toJSON ProjSystem   = String "ProjSystem"

instance ToJSON DataOrRecord where
  toJSON IsData   = String "IsData"
  toJSON IsRecord = String "IsRecord"

instance ToJSON IsInfix where
  toJSON InfixDef   = String "InfixDef"
  toJSON PrefixDef  = String "PrefixDef"

instance ToJSON Access where
  toJSON (PrivateAccess origin) = object
    [ "kind"      .= String "PrivateAccess"
    , "origin"    .= origin
    ]
  toJSON PublicAccess = object
    [ "kind"      .= String "PublicAccess"
    ]
  toJSON OnlyQualified = object
    [ "kind"      .= String "OnlyQualified"
    ]

instance ToJSON IsAbstract where
  toJSON AbstractDef  = String "AbstractDef"
  toJSON ConcreteDef  = String "ConcreteDef"

instance ToJSON IsInstance where
  toJSON InstanceDef    = String "InstanceDef"
  toJSON NotInstanceDef = String "NotInstanceDef"

instance ToJSON IsMacro where
  toJSON MacroDef    = String "MacroDef"
  toJSON NotMacroDef = String "NotMacroDef"

instance ToJSON NameId where
  toJSON (NameId name modul) = object
    [ "name"    .= name
    , "module"  .= modul
    ]

instance ToJSON MetaId where
  toJSON (MetaId i)   = toJSON i

instance ToJSON PositionInName where
  toJSON Beginning  = String "Beginning"
  toJSON Middle     = String "Middle"
  toJSON End        = String "End"

instance ToJSON e => ToJSON (MaybePlaceholder e) where
  toJSON (Placeholder pos) = object
    [ "kind"      .= String "Placeholder"
    , "position"  .= pos
    ]
  toJSON (NoPlaceholder pos value) = object
    [ "kind"      .= String "NoPlaceholder"
    , "position"  .= pos
    , "value"     .= value
    ]

instance ToJSON InteractionId where
  toJSON (InteractionId i) = toJSON i

instance (ToJSON a, ToJSON b) => ToJSON (ImportDirective' a b) where
  toJSON (ImportDirective range using hiding impRenaming publicOpen) = object
    [ "range"       .= range
    , "using"       .= using
    , "hiding"      .= hiding
    , "impRenaming" .= impRenaming
    , "publicOpen"  .= publicOpen
    ]

instance (ToJSON a, ToJSON b) => ToJSON (Using' a b) where
  toJSON UseEverything = Null
  toJSON (Using importedNames) = object
    [ "importedNames"  .= importedNames
    ]

instance (ToJSON a, ToJSON b) => ToJSON (ImportedName' a b) where
  toJSON (ImportedModule value) = object
    [ "kind"        .= String "ImportedModule"
    , "value"       .= value
    ]
  toJSON (ImportedName value) = object
    [ "kind"        .= String "ImportedName"
    , "value"       .= value
    ]

instance (ToJSON a, ToJSON b) => ToJSON (Renaming' a b) where
  toJSON (Renaming from to range) = object
    [ "range"       .= range
    , "from"        .= from
    , "to"          .= to
    ]



instance ToJSON m => ToJSON (TerminationCheck m) where
  toJSON TerminationCheck = object
    [ "kind"      .= String "TerminationCheck"
    ]
  toJSON NoTerminationCheck = object
    [ "kind"      .= String "NoTerminationCheck"
    ]
  toJSON NonTerminating = object
    [ "kind"      .= String "NonTerminating"
    ]
  toJSON Terminating = object
    [ "kind"      .= String "Terminating"
    ]
  toJSON (TerminationMeasure range value) = object
    [ "kind"      .= String "TerminationMeasure"
    , "range"       .= range
    , "value"       .= value
    ]

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

instance ToJSON a => ToJSON (C.OpApp a) where
  toJSON (C.SyntaxBindingLambda range bindings value) = object
    [ "kind"      .= String "SyntaxBindingLambda"
    , "range"     .= range
    , "bindings"  .= bindings
    , "value"     .= value
    ]
  toJSON (C.Ordinary  value) = object
    [ "kind"      .= String "Ordinary"
    , "value"     .= value
    ]

instance ToJSON a => ToJSON (C.FieldAssignment' a) where
  toJSON (C.FieldAssignment name value) = object
    [ "name"      .= name
    , "value"     .= value
    ]

instance ToJSON C.ModuleAssignment where
  toJSON (C.ModuleAssignment name exprs importDirective) = object
    [ "name"            .= name
    , "exprs"           .= exprs
    , "importDirective" .= importDirective
    ]

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

instance ToJSON C.Expr where
  toJSON expr = case expr of
    C.Ident name -> object
      [ "kind"      .= String "Ident"
      , "name"      .= name
      ]
    C.Lit literal -> object
      [ "kind"      .= String "Lit"
      , "literal"   .= literal
      ]
    C.QuestionMark range index -> object
      [ "kind"      .= String "QuestionMark"
      , "range"     .= range
      , "index"     .= index
      ]
    C.Underscore range name -> object
      [ "kind"      .= String "Underscore"
      , "range"     .= range
      , "name"      .= name
      ]
    C.RawApp range exprs -> object
      [ "kind"      .= String "RawApp"
      , "range"     .= range
      , "exprs"     .= exprs
      ]
    C.App range expr args -> object
      [ "kind"      .= String "App"
      , "range"     .= range
      , "expr"      .= expr
      , "args"      .= args
      ]
    C.OpApp range name names args -> object
      [ "kind"      .= String "OpApp"
      , "range"     .= range
      , "name"      .= name
      , "names"     .= names
      , "args"      .= args
      ]
    C.WithApp range expr exprs -> object
      [ "kind"      .= String "WithApp"
      , "range"     .= range
      , "expr"      .= expr
      , "exprs"     .= exprs
      ]
    C.HiddenArg range expr -> object
      [ "kind"      .= String "HiddenArg"
      , "range"     .= range
      , "expr"      .= expr
      ]
    C.InstanceArg range expr -> object
      [ "kind"      .= String "InstanceArg"
      , "range"     .= range
      , "expr"      .= expr
      ]
    C.Lam range binding expr -> object
      [ "kind"      .= String "Lam"
      , "range"     .= range
      , "binding"   .= binding
      , "expr"      .= expr
      ]
    C.AbsurdLam range hiding -> object
      [ "kind"      .= String "AbsurdLam"
      , "range"     .= range
      , "hiding"    .= hiding
      ]
    C.ExtendedLam range clauses -> object
      [ "kind"      .= String "ExtendedLam"
      , "range"     .= range
      , "clauses"   .= clauses
      ]
    C.Fun range arg expr -> object
      [ "kind"      .= String "Fun"
      , "range"     .= range
      , "arg"       .= arg
      , "expr"      .= expr
      ]
    C.Pi telescope expr -> object
      [ "kind"      .= String "Pi"
      , "telescope" .= telescope
      , "expr"      .= expr
      ]
    C.Set range -> object
      [ "kind"      .= String "Set"
      , "range"     .= range
      ]
    C.Prop range -> object
      [ "kind"      .= String "Prop"
      , "range"     .= range
      ]
    C.SetN range level -> object
      [ "kind"      .= String "SetN"
      , "range"     .= range
      , "level"     .= level
      ]
    C.PropN range level -> object
      [ "kind"      .= String "PropN"
      , "range"     .= range
      , "level"     .= level
      ]
    C.Rec range assignments -> object
      [ "kind"        .= String "Rec"
      , "range"       .= range
      , "assignments" .= assignments
      ]
    C.RecUpdate range expr assignments -> object
      [ "kind"        .= String "RecUpdate"
      , "range"       .= range
      , "expr"        .= expr
      , "assignments" .= assignments
      ]
    C.Let range declarations expr -> object
      [ "kind"          .= String "Let"
      , "range"         .= range
      , "declarations"  .= declarations
      , "expr"          .= expr
      ]
    C.Paren range expr -> object
      [ "kind"      .= String "Paren"
      , "range"     .= range
      , "expr"      .= expr
      ]
    C.IdiomBrackets range expr -> object
      [ "kind"      .= String "IdiomBrackets"
      , "range"     .= range
      , "expr"      .= expr
      ]
    C.DoBlock range dostmts -> object
      [ "kind"      .= String "DoBlock"
      , "range"     .= range
      , "dostmts"   .= dostmts
      ]
    C.Absurd range -> object
      [ "kind"      .= String "Absurd"
      , "range"     .= range
      ]
    C.As range name expr -> object
      [ "kind"      .= String "As"
      , "range"     .= range
      , "name"      .= name
      , "expr"      .= expr
      ]
    C.Dot range expr -> object
      [ "kind"      .= String "Dot"
      , "range"     .= range
      , "expr"      .= expr
      ]
    C.ETel telescope -> object
      [ "kind"      .= String "ETel"
      , "telescope" .= telescope
      ]
    C.QuoteGoal range name expr -> object
      [ "kind"      .= String "QuoteGoal"
      , "range"     .= range
      , "name"      .= name
      , "expr"      .= expr
      ]
    C.QuoteContext range -> object
      [ "kind"      .= String "QuoteContext"
      , "range"     .= range
      ]
    C.Quote range -> object
      [ "kind"      .= String "Quote"
      , "range"     .= range
      ]
    C.QuoteTerm range -> object
      [ "kind"      .= String "QuoteTerm"
      , "range"     .= range
      ]
    C.Tactic range expr exprs -> object
      [ "kind"      .= String "Tactic"
      , "range"     .= range
      , "expr"      .= expr
      , "exprs"     .= exprs
      ]
    C.Unquote range -> object
      [ "kind"      .= String "Unquote"
      , "range"     .= range
      ]
    C.DontCare expr -> object
      [ "kind"      .= String "DontCare"
      , "expr"     .= expr
      ]
    C.Equal range expr1 expr2 -> object
      [ "kind"      .= String "Equal"
      , "range"     .= range
      , "expr1"     .= expr1
      , "expr2"     .= expr2
      ]
    C.Ellipsis range -> object
      [ "kind"      .= String "Ellipsis"
      , "range"     .= range
      ]
    C.Generalized range -> object
      [ "kind"      .= String "Generalized"
      , "expr"      .= expr
      ]

instance ToJSON C.Pattern where
  toJSON pattern = case pattern of
    C.IdentP name -> object
      [ "kind"      .= String "IdentP"
      , "name"      .= name
      ]
    C.QuoteP range -> object
      [ "kind"      .= String "QuoteP"
      , "range"     .= range
      ]
    C.AppP pattern arg -> object
      [ "kind"      .= String "AppP"
      , "pattern"   .= pattern
      , "arg"       .= arg
      ]
    C.RawAppP range patterns -> object
      [ "kind"      .= String "RawAppP"
      , "range"     .= range
      , "patterns"  .= patterns
      ]
    C.OpAppP range name names args -> object
      [ "kind"      .= String "OpAppP"
      , "range"     .= range
      , "name"      .= name
      , "names"     .= names
      , "args"      .= args
      ]
    C.HiddenP range pattern -> object
      [ "kind"      .= String "HiddenP"
      , "range"     .= range
      , "pattern"   .= pattern
      ]
    C.InstanceP range pattern -> object
      [ "kind"      .= String "InstanceP"
      , "range"     .= range
      , "pattern"   .= pattern
      ]
    C.ParenP range pattern -> object
      [ "kind"      .= String "ParenP"
      , "range"     .= range
      , "pattern"   .= pattern
      ]
    C.WildP range -> object
      [ "kind"      .= String "WildP"
      , "range"     .= range
      ]
    C.AbsurdP range -> object
      [ "kind"      .= String "AbsurdP"
      , "range"     .= range
      ]
    C.AsP range name pattern -> object
      [ "kind"      .= String "AsP"
      , "range"     .= range
      , "name"      .= name
      , "pattern"   .= pattern
      ]
    C.DotP range expr -> object
      [ "kind"      .= String "DotP"
      , "range"     .= range
      , "expr"      .= expr
      ]
    C.LitP literal -> object
      [ "kind"      .= String "LitP"
      , "literal"   .= literal
      ]
    C.RecP range assignments -> object
      [ "kind"        .= String "RecP"
      , "range"       .= range
      , "assignments" .= assignments
      ]
    C.EqualP range pairs -> object
      [ "kind"      .= String "EqualP"
      , "range"     .= range
      , "pairs"     .= pairs
      ]
    C.EllipsisP range -> object
      [ "kind"      .= String "EllipsisP"
      , "range"     .= range
      ]
    C.WithP range pattern -> object
      [ "kind"      .= String "WithP"
      , "range"     .= range
      , "pattern"   .= pattern
      ]

instance ToJSON C.DoStmt where
  toJSON (C.DoBind range pattern expr clauses) = object
    [ "kind"      .= String "DoBind"
    , "range"     .= range
    , "pattern"   .= pattern
    , "expr"      .= expr
    , "clauses"   .= clauses
    ]
  toJSON (C.DoThen expr) = object
    [ "kind"      .= String "DoThen"
    , "expr"      .= expr
    ]
  toJSON (C.DoLet range declarations) = object
    [ "kind"          .= String "DoLet"
    , "range"         .= range
    , "declarations"  .= declarations
    ]

instance ToJSON a => ToJSON (C.LamBinding' a) where
  toJSON (C.DomainFree argInfo name) = object
    [ "kind"      .= String "DomainFree"
    , "argInfo"   .= argInfo
    , "name"      .= name
    ]
  toJSON (C.DomainFull value) = object
    [ "kind"      .= String "DomainFull"
    , "value"     .= value
    ]


instance ToJSON a => ToJSON (C.TypedBindings' a) where
  toJSON (C.TypedBindings range arg) = object
    [ "range"     .= range
    , "arg"       .= arg
    ]

instance ToJSON C.BoundName where
  toJSON (C.BName name label fixity) = object
    [ "name"      .= name
    , "label"     .= label
    , "fixity"    .= fixity
    ]

instance ToJSON a => ToJSON (C.TypedBinding' a) where
  toJSON (C.TBind range bindings value) = object
    [ "kind"      .= String "TBind"
    , "range"     .= range
    , "bindings"  .= bindings
    , "value"     .= value
    ]
  toJSON (C.TLet range declarations) = object
    [ "kind"          .= String "TLet"
    , "range"         .= range
    , "declarations"  .= declarations
    ]

instance ToJSON C.LHS where
  toJSON (C.LHS pattern rewrites withExpr) = object
    [ "OriginalPattern" .= pattern
    , "RewriteEqn"      .= rewrites
    , "withExpr"        .= withExpr
    ]

instance ToJSON C.LHSCore where
  toJSON (C.LHSHead name patterns) = object
    [ "kind"            .= String "LHSHead"
    , "name"            .= name
    , "patterns"        .= patterns
    ]
  toJSON (C.LHSProj name patternsLeft focus patterns) = object
    [ "kind"            .= String "LHSProj"
    , "name"            .= name
    , "patternsLeft"     .= patternsLeft
    , "focus"           .= focus
    , "patterns"        .= patterns
    ]
  toJSON (C.LHSWith head withPatterns patterns) = object
    [ "kind"            .= String "LHSWith"
    , "head"            .= head
    , "withPatterns"    .= withPatterns
    , "patterns"        .= patterns
    ]

instance ToJSON a => ToJSON (C.RHS' a) where
  toJSON C.AbsurdRHS = object
    [ "kind"            .= String "AbsurdRHS"
    ]
  toJSON (C.RHS value) = object
    [ "kind"            .= String "RHS"
    , "value"           .= value
    ]

instance ToJSON a => ToJSON (C.WhereClause' a) where
  toJSON C.NoWhere = object
    [ "kind"            .= String "NoWhere"
    ]
  toJSON (C.AnyWhere declarations) = object
    [ "kind"            .= String "AnyWhere"
    , "declarations"    .= declarations
    ]
  toJSON (C.SomeWhere name access declarations) = object
    [ "kind"            .= String "SomeWhere"
    , "name"            .= name
    , "access"          .= access
    , "declarations"    .= declarations
    ]


instance ToJSON C.LamClause where
  toJSON (C.LamClause lhs rhs whereClause catchAll) = object
    [ "LHS"             .= lhs
    , "RHS"             .= rhs
    , "whereClause"     .= whereClause
    , "catchAll"        .= catchAll
    ]

instance ToJSON C.ExprWhere where
  toJSON (C.ExprWhere expr whereClause) = object
    [ "expr"            .= expr
    , "whereClause"     .= whereClause
    ]

instance ToJSON C.AsName where
  toJSON (C.AsName name range) = object
    [ "name"            .= name
    , "range"           .= range
    ]

instance ToJSON C.Declaration where
  toJSON declaration = case declaration of
    C.TypeSig argInfo name expr -> object
      [ "kind"            .= String "TypeSig"
      , "argInfo"         .= argInfo
      , "name"            .= name
      , "expr"            .= expr
      ]
    C.Generalize argInfo name expr -> object
      [ "kind"            .= String "Generalize"
      , "argInfo"         .= argInfo
      , "name"            .= name
      , "expr"            .= expr
      ]
    C.Field inst name arg -> object
      [ "kind"            .= String "Field"
      , "instance"        .= inst
      , "name"            .= name
      , "arg"             .= arg
      ]
    C.FunClause lhs rhs whereClause catchAll -> object
      [ "kind"            .= String "FunClause"
      , "LHS"             .= lhs
      , "RHS"             .= rhs
      , "whereClause"     .= whereClause
      , "catchAll"        .= catchAll
      ]
    C.DataSig range induction name bindings expr -> object
      [ "kind"            .= String "DataSig"
      , "range"           .= range
      , "induction"       .= induction
      , "name"            .= name
      , "bindings"        .= bindings
      , "expr"            .= expr
      ]
    C.Data range induction name bindings expr typSigOrInsBlks -> object
      [ "kind"            .= String "Data"
      , "range"           .= range
      , "induction"       .= induction
      , "name"            .= name
      , "bindings"        .= bindings
      , "expr"            .= expr
      , "typSigOrInsBlks" .= typSigOrInsBlks
      ]
    C.RecordSig range name bindings expr -> object
      [ "kind"            .= String "RecordSig"
      , "range"           .= range
      , "name"            .= name
      , "bindings"        .= bindings
      , "expr"            .= expr
      ]
    C.Record range name induction hasEta instancePairs bindings expr declarations
      -> object
        [ "kind"            .= String "Record"
        , "range"           .= range
        , "name"            .= name
        , "induction"       .= induction
        , "hasEta"          .= hasEta
        , "instancePairs"   .= instancePairs
        , "bindings"        .= bindings
        , "expr"            .= expr
        , "declarations"    .= declarations
        ]
    C.Infix fixity names -> object
      [ "kind"            .= String "Field"
      , "fixity"          .= fixity
      , "names"           .= names
      ]
    C.Syntax name notation -> object
      [ "kind"            .= String "Syntax"
      , "name"            .= name
      , "notation"        .= notation
      ]
    C.PatternSyn range name args pattern -> object
      [ "kind"            .= String "PatternSyn"
      , "range"           .= range
      , "name"            .= name
      , "args"            .= args
      , "pattern"         .= pattern
      ]
    C.Mutual range declarations -> object
      [ "kind"            .= String "Mutual"
      , "range"           .= range
      , "declarations"    .= declarations
      ]
    C.Abstract range declarations -> object
      [ "kind"            .= String "Abstract"
      , "range"           .= range
      , "declarations"    .= declarations
      ]
    C.Private range origin declarations -> object
      [ "kind"            .= String "Private"
      , "range"           .= range
      , "origin"          .= origin
      , "declarations"    .= declarations
      ]
    C.InstanceB range declarations -> object
      [ "kind"            .= String "InstanceB"
      , "range"           .= range
      , "declarations"    .= declarations
      ]
    C.Macro range declarations -> object
      [ "kind"            .= String "Macro"
      , "range"           .= range
      , "declarations"    .= declarations
      ]
    C.Postulate range typSigOrInsBlks -> object
      [ "kind"            .= String "Postulate"
      , "range"           .= range
      , "typSigOrInsBlks" .= typSigOrInsBlks
      ]
    C.Primitive range typeSigs -> object
      [ "kind"            .= String "Primitive"
      , "range"           .= range
      , "typeSigs"        .= typeSigs
      ]
    C.Open range name importDirective -> object
      [ "kind"            .= String "Primitive"
      , "range"           .= range
      , "name"            .= name
      , "importDirective" .= importDirective
      ]
    C.Import range name asName openShortHand importDirective -> object
      [ "kind"            .= String "Import"
      , "range"           .= range
      , "name"            .= name
      , "asName"          .= asName
      , "openShortHand"   .= openShortHand
      , "importDirective" .= importDirective
      ]
    C.ModuleMacro range name moduleApp openShortHand importDirective -> object
      [ "kind"            .= String "ModuleMacro"
      , "range"           .= range
      , "name"            .= name
      , "moduleApp"       .= moduleApp
      , "openShortHand"   .= openShortHand
      , "importDirective" .= importDirective
      ]
    C.Module range name bindings declarations -> object
      [ "kind"            .= String "Module"
      , "range"           .= range
      , "name"            .= name
      , "bindings"        .= bindings
      , "declarations"    .= declarations
      ]
    C.UnquoteDecl range names expr -> object
      [ "kind"            .= String "UnquoteDecl"
      , "range"           .= range
      , "names"           .= names
      , "expr"            .= expr
      ]
    C.UnquoteDef range names expr -> object
      [ "kind"            .= String "UnquoteDef"
      , "range"           .= range
      , "names"           .= names
      , "expr"            .= expr
      ]
    C.Pragma pragma -> object
      [ "kind"            .= String "Pragma"
      , "pragma"          .= pragma
      ]


instance ToJSON C.ModuleApplication where
  toJSON (C.SectionApp range bindings expr) = object
    [ "kind"      .= String "SectionApp"
    , "range"     .= range
    , "bindings"  .= bindings
    , "expr"      .= expr
    ]
  toJSON (C.RecordModuleIFS range name) = object
    [ "kind"      .= String "RecordModuleIFS"
    , "range"     .= range
    , "name"      .= name
    ]

instance ToJSON C.OpenShortHand where
  toJSON C.DoOpen   = String "DoOpen"
  toJSON C.DontOpen = String "DontOpen"

instance ToJSON C.Pragma where
  toJSON pragma = case pragma of
    C.OptionsPragma range options -> object
      [ "kind"      .= String "OptionsPragma"
      , "range"     .= range
      , "options"      .= options
      ]
    C.BuiltinPragma range entity name fixity -> object
      [ "kind"      .= String "BuiltinPragma"
      , "range"     .= range
      , "entity"    .= entity
      , "name"      .= name
      , "fixity"    .= fixity
      ]
    C.RewritePragma range name -> object
      [ "kind"      .= String "RewritePragma"
      , "range"     .= range
      , "name"      .= name
      ]
    C.CompiledDataPragma range name hd hcs -> object
      [ "kind"          .= String "CompiledDataPragma"
      , "range"         .= range
      , "name"          .= name
      , "data"          .= hd
      , "constructors"  .= hcs
      ]
    C.CompiledTypePragma range name ht -> object
      [ "kind"          .= String "CompiledTypePragma"
      , "range"         .= range
      , "name"          .= name
      , "type"          .= ht
      ]
    C.CompiledPragma range name hs -> object
      [ "kind"          .= String "CompiledPragma"
      , "range"         .= range
      , "name"          .= name
      , "haskell"       .= hs
      ]
    C.CompiledExportPragma range name export -> object
      [ "kind"          .= String "CompiledExportPragma"
      , "range"         .= range
      , "name"          .= name
      , "export"        .= export
      ]
    C.CompiledJSPragma range name js -> object
      [ "kind"          .= String "CompiledJSPragma"
      , "range"         .= range
      , "name"          .= name
      , "js"            .= js
      ]
    C.CompiledUHCPragma range name uhc -> object
      [ "kind"          .= String "CompiledUHCPragma"
      , "range"         .= range
      , "name"          .= name
      , "uhc"           .= uhc
      ]
    C.CompiledDataUHCPragma range name uhcd uhccs -> object
      [ "kind"          .= String "CompiledDataUHCPragma"
      , "range"         .= range
      , "name"          .= name
      , "data"          .= uhcd
      , "constructors"  .= uhccs
      ]
    C.HaskellCodePragma range code -> object
      [ "kind"          .= String "HaskellCodePragma"
      , "range"         .= range
      , "code"          .= code
      ]
    C.ForeignPragma range backend code -> object
      [ "kind"          .= String "ForeignPragma"
      , "range"         .= range
      , "backend"       .= backend
      , "code"          .= code
      ]
    C.CompilePragma range backend name code -> object
      [ "kind"          .= String "CompilePragma"
      , "range"         .= range
      , "backend"       .= backend
      , "name"          .= name
      , "code"          .= code
      ]
    C.StaticPragma range name -> object
      [ "kind"          .= String "StaticPragma"
      , "range"         .= range
      , "name"          .= name
      ]
    C.InjectivePragma range name -> object
      [ "kind"          .= String "InjectivePragma"
      , "range"         .= range
      , "name"          .= name
      ]
    C.InlinePragma range inline name -> object
      [ "kind"          .= String "InlinePragma"
      , "range"         .= range
      , "inline"        .= inline
      , "name"          .= name
      ]
    C.ImportPragma range hsm -> object
      [ "kind"          .= String "ImportPragma"
      , "range"         .= range
      , "module"        .= hsm
      ]
    C.ImportUHCPragma range uhcsm -> object
      [ "kind"          .= String "ImportUHCPragma"
      , "range"         .= range
      , "module"        .= uhcsm
      ]
    C.ImpossiblePragma range -> object
      [ "kind"          .= String "ImpossiblePragma"
      , "range"         .= range
      ]
    C.EtaPragma range name -> object
      [ "kind"          .= String "EtaPragma"
      , "range"         .= range
      , "name"          .= name
      ]
    C.TerminationCheckPragma range name -> object
      [ "kind"          .= String "TerminationCheckPragma"
      , "range"         .= range
      , "name"          .= name
      ]
    C.WarningOnUsage range name warning -> object
      [ "kind"          .= String "WarningOnUsage"
      , "range"         .= range
      , "name"          .= name
      , "warning"       .= warning
      ]
    C.CatchallPragma range -> object
      [ "kind"          .= String "CatchallPragma"
      , "range"         .= range
      ]
    C.DisplayPragma range pattern expr -> object
      [ "kind"          .= String "DisplayPragma"
      , "range"         .= range
      , "pattern"       .= pattern
      , "expr"          .= expr
      ]
    C.NoPositivityCheckPragma range -> object
      [ "kind"          .= String "NoPositivityCheckPragma"
      , "range"         .= range
      ]
    C.PolarityPragma range name occurrences -> object
      [ "kind"          .= String "PolarityPragma"
      , "range"         .= range
      , "name"          .= name
      , "occurrences"   .= occurrences
      ]
    C.NoUniverseCheckPragma range -> object
      [ "kind"          .= String "NoUniverseCheckPragma"
      , "range"         .= range
      ]

--------------------------------------------------------------------------------
-- Agda.Syntax.Fixity

instance ToJSON F.NotationSection where
  toJSON (F.NotationSection notation kind level isSection) = object
    [ "notation"  .= notation
    , "kind"      .= kind
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
    , "source"    .= src
    ]
  toJSON P.NoRange = object
    [ "intervals" .= ([] :: [P.Interval' a])
    ]
