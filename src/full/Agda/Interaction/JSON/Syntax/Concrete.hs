{-# LANGUAGE OverloadedStrings #-}

-- | Instances of EncodeTCM or ToJSON under Agda.Syntax.Concrete

module Agda.Interaction.JSON.Syntax.Concrete where

import Data.Aeson

import Agda.Interaction.JSON.Encode
import Agda.Interaction.JSON.Syntax.Concrete.Name
import Agda.Interaction.JSON.Syntax.Fixity
import Agda.Interaction.JSON.Syntax.Literal
import Agda.Interaction.JSON.Syntax.Position
import Agda.Interaction.JSON.TypeChecking.Positivity

import Agda.Syntax.Concrete
import Agda.Syntax.Concrete.Pretty (smashTel)
import Agda.Syntax.Concrete.Definitions

--------------------------------------------------------------------------------

instance ToJSON a => ToJSON (OpApp a) where
  toJSON (SyntaxBindingLambda range bindings value) = kind' "SyntaxBindingLambda"
    [ "range"     .= range
    , "bindings"  .= bindings
    , "value"     .= value
    ]
  toJSON (Ordinary  value) = kind' "Ordinary"
    [ "value"     .= value
    ]

instance ToJSON a => ToJSON (FieldAssignment' a) where
  toJSON (FieldAssignment name value) = object
    [ "name"      .= name
    , "value"     .= value
    ]

instance ToJSON ModuleAssignment where
  toJSON (ModuleAssignment name exprs importDirective) = object
    [ "name"            .= name
    , "exprs"           .= exprs
    , "importDirective" .= importDirective
    ]

instance EncodeTCM Expr where
instance ToJSON Expr where
  toJSON expr = case expr of
    Ident name -> kind' "Ident"
      [ "name"      .= name
      ]
    Lit literal -> kind' "Lit"
      [ "literal"   .= literal
      ]
    QuestionMark range index -> kind' "QuestionMark"
      [ "range"     .= range
      , "index"     .= index
      ]
    Underscore range name -> kind' "Underscore"
      [ "range"     .= range
      , "name"      .= name
      ]
    RawApp range exprs -> kind' "RawApp"
      [ "range"     .= range
      , "exprs"     .= exprs
      ]
    App range expr args -> kind' "App"
      [ "range"     .= range
      , "expr"      .= expr
      , "args"      .= args
      ]
    OpApp range name names args -> kind' "OpApp"
      [ "range"     .= range
      , "name"      .= name
      , "names"     .= names
      , "args"      .= args
      ]
    WithApp range expr exprs -> kind' "WithApp"
      [ "range"     .= range
      , "expr"      .= expr
      , "exprs"     .= exprs
      ]
    HiddenArg range expr -> kind' "HiddenArg"
      [ "range"     .= range
      , "expr"      .= expr
      ]
    InstanceArg range expr -> kind' "InstanceArg"
      [ "range"     .= range
      , "expr"      .= expr
      ]
    Lam range bindings expr -> kind' "Lam"
      [ "range"     .= range
      , "bindings"  .= bindings
      , "expr"      .= expr
      ]
    AbsurdLam range hiding -> kind' "AbsurdLam"
      [ "range"     .= range
      , "hiding"    .= hiding
      ]
    ExtendedLam range clauses -> kind' "ExtendedLam"
      [ "range"     .= range
      , "clauses"   .= clauses
      ]
    Fun range arg expr -> kind' "Fun"
      [ "range"     .= range
      , "arg"       .= arg
      , "expr"      .= expr
      ]
    Pi telescope expr -> kind' "Pi"
      [ "telescope" .= smashTel telescope
      , "expr"      .= expr
      ]
    Set range -> kind' "Set"
      [ "range"     .= range
      ]
    Prop range -> kind' "Prop"
      [ "range"     .= range
      ]
    SetN range level -> kind' "SetN"
      [ "range"     .= range
      , "level"     .= level
      ]
    PropN range level -> kind' "PropN"
      [ "range"     .= range
      , "level"     .= level
      ]
    Rec range assignments -> kind' "Rec"
      [ "range"       .= range
      , "assignments" .= assignments
      ]
    RecUpdate range expr assignments -> kind' "RecUpdate"
      [ "range"       .= range
      , "expr"        .= expr
      , "assignments" .= assignments
      ]
    Let range declarations expr -> kind' "Let"
      [ "range"         .= range
      , "declarations"  .= declarations
      , "expr"          .= expr
      ]
    Paren range expr -> kind' "Paren"
      [ "range"     .= range
      , "expr"      .= expr
      ]
    IdiomBrackets range expr -> kind' "IdiomBrackets"
      [ "range"     .= range
      , "expr"      .= expr
      ]
    DoBlock range dostmts -> kind' "DoBlock"
      [ "range"     .= range
      , "dostmts"   .= dostmts
      ]
    Absurd range -> kind' "Absurd"
      [ "range"     .= range
      ]
    As range name expr -> kind' "As"
      [ "range"     .= range
      , "name"      .= name
      , "expr"      .= expr
      ]
    Dot range expr -> kind' "Dot"
      [ "range"     .= range
      , "expr"      .= expr
      ]
    ETel telescope -> kind' "ETel"
      [ "telescope" .= telescope
      ]
    QuoteGoal range name expr -> kind' "QuoteGoal"
      [ "range"     .= range
      , "name"      .= name
      , "expr"      .= expr
      ]
    QuoteContext range -> kind' "QuoteContext"
      [ "range"     .= range
      ]
    Quote range -> kind' "Quote"
      [ "range"     .= range
      ]
    QuoteTerm range -> kind' "QuoteTerm"
      [ "range"     .= range
      ]
    Tactic range expr exprs -> kind' "Tactic"
      [ "range"     .= range
      , "expr"      .= expr
      , "exprs"     .= exprs
      ]
    Unquote range -> kind' "Unquote"
      [ "range"     .= range
      ]
    DontCare expr -> kind' "DontCare"
      [ "expr"     .= expr
      ]
    Equal range expr1 expr2 -> kind' "Equal"
      [ "range"     .= range
      , "expr1"     .= expr1
      , "expr2"     .= expr2
      ]
    Ellipsis range -> kind' "Ellipsis"
      [ "range"     .= range
      ]
    Generalized range -> kind' "Generalized"
      [ "expr"      .= expr
      ]

instance EncodeTCM Pattern where
instance ToJSON Pattern where
  toJSON pattern = case pattern of
    IdentP name -> kind' "IdentP"
      [ "name"      .= name
      ]
    QuoteP range -> kind' "QuoteP"
      [ "range"     .= range
      ]
    AppP pattern arg -> kind' "AppP"
      [ "pattern"   .= pattern
      , "arg"       .= arg
      ]
    RawAppP range patterns -> kind' "RawAppP"
      [ "range"     .= range
      , "patterns"  .= patterns
      ]
    OpAppP range name names args -> kind' "OpAppP"
      [ "range"     .= range
      , "name"      .= name
      , "names"     .= names
      , "args"      .= args
      ]
    HiddenP range pattern -> kind' "HiddenP"
      [ "range"     .= range
      , "pattern"   .= pattern
      ]
    InstanceP range pattern -> kind' "InstanceP"
      [ "range"     .= range
      , "pattern"   .= pattern
      ]
    ParenP range pattern -> kind' "ParenP"
      [ "range"     .= range
      , "pattern"   .= pattern
      ]
    WildP range -> kind' "WildP"
      [ "range"     .= range
      ]
    AbsurdP range -> kind' "AbsurdP"
      [ "range"     .= range
      ]
    AsP range name pattern -> kind' "AsP"
      [ "range"     .= range
      , "name"      .= name
      , "pattern"   .= pattern
      ]
    DotP range expr -> kind' "DotP"
      [ "range"     .= range
      , "expr"      .= expr
      ]
    LitP literal -> kind' "LitP"
      [ "literal"   .= literal
      ]
    RecP range assignments -> kind' "RecP"
      [ "range"       .= range
      , "assignments" .= assignments
      ]
    EqualP range pairs -> kind' "EqualP"
      [ "range"     .= range
      , "pairs"     .= pairs
      ]
    EllipsisP range -> kind' "EllipsisP"
      [ "range"     .= range
      ]
    WithP range pattern -> kind' "WithP"
      [ "range"     .= range
      , "pattern"   .= pattern
      ]

instance ToJSON DoStmt where
  toJSON (DoBind range pattern expr clauses) = kind' "DoBind"
    [ "range"     .= range
    , "pattern"   .= pattern
    , "expr"      .= expr
    , "clauses"   .= clauses
    ]
  toJSON (DoThen expr) = kind' "DoThen"
    [ "expr"      .= expr
    ]
  toJSON (DoLet range declarations) = kind' "DoLet"
    [ "range"         .= range
    , "declarations"  .= declarations
    ]

instance ToJSON a => ToJSON (LamBinding' a) where
  toJSON (DomainFree argInfo name) = kind' "DomainFree"
    [ "argInfo"   .= argInfo
    , "name"      .= name
    ]
  toJSON (DomainFull value) = kind' "DomainFull"
    [ "value"     .= value
    ]


instance EncodeTCM TypedBindings where
instance ToJSON a => ToJSON (TypedBindings' a) where
  toJSON (TypedBindings range arg) = object
    [ "range"     .= range
    , "arg"       .= arg
    ]

instance ToJSON BoundName where
  toJSON (BName name label fixity) = object
    [ "name"      .= name
    , "label"     .= label
    , "fixity"    .= fixity
    ]

instance EncodeTCM TypedBinding where
instance ToJSON a => ToJSON (TypedBinding' a) where
  toJSON (TBind range bindings value) = kind' "TBind"
    [ "range"     .= range
    , "bindings"  .= bindings
    , "value"     .= value
    ]
  toJSON (TLet range declarations) = kind' "TLet"
    [ "range"         .= range
    , "declarations"  .= declarations
    ]

instance ToJSON LHS where
  toJSON (LHS pattern rewrites withExpr) = object
    [ "originalPattern" .= pattern
    , "rewriteEqn"      .= rewrites
    , "withExpr"        .= withExpr
    ]

instance ToJSON LHSCore where
  toJSON (LHSHead name patterns) = kind' "LHSHead"
    [ "name"            .= name
    , "patterns"        .= patterns
    ]
  toJSON (LHSProj name patternsLeft focus patterns) = kind' "LHSProj"
    [ "name"            .= name
    , "patternsLeft"     .= patternsLeft
    , "focus"           .= focus
    , "patterns"        .= patterns
    ]
  toJSON (LHSWith head withPatterns patterns) = kind' "LHSWith"
    [ "head"            .= head
    , "withPatterns"    .= withPatterns
    , "patterns"        .= patterns
    ]

instance ToJSON a => ToJSON (RHS' a) where
  toJSON AbsurdRHS = kind' "AbsurdRHS" []
  toJSON (RHS value) = kind' "RHS"
    [ "value"           .= value
    ]

instance ToJSON a => ToJSON (WhereClause' a) where
  toJSON NoWhere = kind' "NoWhere" []
  toJSON (AnyWhere declarations) = kind' "AnyWhere"
    [ "declarations"    .= declarations
    ]
  toJSON (SomeWhere name access declarations) = kind' "SomeWhere"
    [ "name"            .= name
    , "access"          .= access
    , "declarations"    .= declarations
    ]


instance ToJSON LamClause where
  toJSON (LamClause lhs rhs whereClause catchAll) = object
    [ "LHS"             .= lhs
    , "RHS"             .= rhs
    , "whereClause"     .= whereClause
    , "catchAll"        .= catchAll
    ]

instance ToJSON ExprWhere where
  toJSON (ExprWhere expr whereClause) = object
    [ "expr"            .= expr
    , "whereClause"     .= whereClause
    ]

instance ToJSON AsName where
  toJSON (AsName name range) = object
    [ "name"            .= name
    , "range"           .= range
    ]

instance EncodeTCM Declaration where
instance ToJSON Declaration where
  toJSON declaration = case declaration of
    TypeSig argInfo name expr -> kind' "TypeSig"
      [ "argInfo"         .= argInfo
      , "name"            .= name
      , "expr"            .= expr
      ]
    Generalize argInfo name expr -> kind' "Generalize"
      [ "argInfo"         .= argInfo
      , "name"            .= name
      , "expr"            .= expr
      ]
    Field inst name arg -> kind' "Field"
      [ "instance"        .= inst
      , "name"            .= name
      , "arg"             .= arg
      ]
    FunClause lhs rhs whereClause catchAll -> kind' "FunClause"
      [ "LHS"             .= lhs
      , "RHS"             .= rhs
      , "whereClause"     .= whereClause
      , "catchAll"        .= catchAll
      ]
    DataSig range induction name bindings expr -> kind' "DataSig"
      [ "range"           .= range
      , "induction"       .= induction
      , "name"            .= name
      , "bindings"        .= bindings
      , "expr"            .= expr
      ]
    Data range induction name bindings expr declarations -> kind' "Data"
      [ "range"           .= range
      , "induction"       .= induction
      , "name"            .= name
      , "bindings"        .= bindings
      , "expr"            .= expr
      , "declarations"    .= declarations
      ]
    RecordSig range name bindings expr -> kind' "RecordSig"
      [ "range"           .= range
      , "name"            .= name
      , "bindings"        .= bindings
      , "expr"            .= expr
      ]
    Record range name induction hasEta instancePairs bindings expr declarations
      -> kind' "Record"
        [ "range"           .= range
        , "name"            .= name
        , "induction"       .= induction
        , "hasEta"          .= hasEta
        , "instancePairs"   .= instancePairs
        , "bindings"        .= bindings
        , "expr"            .= expr
        , "declarations"    .= declarations
        ]
    Infix fixity names -> kind' "Field"
      [ "fixity"          .= fixity
      , "names"           .= names
      ]
    Syntax name notation -> kind' "Syntax"
      [ "name"            .= name
      , "notation"        .= notation
      ]
    PatternSyn range name args pattern -> kind' "PatternSyn"
      [ "range"           .= range
      , "name"            .= name
      , "args"            .= args
      , "pattern"         .= pattern
      ]
    Mutual range declarations -> kind' "Mutual"
      [ "range"           .= range
      , "declarations"    .= declarations
      ]
    Abstract range declarations -> kind' "Abstract"
      [ "range"           .= range
      , "declarations"    .= declarations
      ]
    Private range origin declarations -> kind' "Private"
      [ "range"           .= range
      , "origin"          .= origin
      , "declarations"    .= declarations
      ]
    InstanceB range declarations -> kind' "InstanceB"
      [ "range"           .= range
      , "declarations"    .= declarations
      ]
    Macro range declarations -> kind' "Macro"
      [ "range"           .= range
      , "declarations"    .= declarations
      ]
    Postulate range declarations -> kind' "Postulate"
      [ "range"           .= range
      , "declarations"    .= declarations
      ]
    Primitive range declarations -> kind' "Primitive"
      [ "range"           .= range
      , "declarations"    .= declarations
      ]
    Open range name importDirective -> kind' "Open"
      [ "range"           .= range
      , "name"            .= name
      , "importDirective" .= importDirective
      ]
    Import range name asName openShortHand importDirective -> kind' "Import"
      [ "range"           .= range
      , "name"            .= name
      , "asName"          .= asName
      , "openShortHand"   .= openShortHand
      , "importDirective" .= importDirective
      ]
    ModuleMacro range name moduleApp openShortHand importDirective -> kind' "ModuleMacro"
      [ "range"           .= range
      , "name"            .= name
      , "moduleApp"       .= moduleApp
      , "openShortHand"   .= openShortHand
      , "importDirective" .= importDirective
      ]
    Module range name bindings declarations -> kind' "Module"
      [ "range"           .= range
      , "name"            .= name
      , "bindings"        .= bindings
      , "declarations"    .= declarations
      ]
    UnquoteDecl range names expr -> kind' "UnquoteDecl"
      [ "range"           .= range
      , "names"           .= names
      , "expr"            .= expr
      ]
    UnquoteDef range names expr -> kind' "UnquoteDef"
      [ "range"           .= range
      , "names"           .= names
      , "expr"            .= expr
      ]
    Pragma pragma -> kind' "Pragma"
      [ "pragma"          .= pragma
      ]


instance ToJSON ModuleApplication where
  toJSON (SectionApp range bindings expr) = kind' "SectionApp"
    [ "range"     .= range
    , "bindings"  .= bindings
    , "expr"      .= expr
    ]
  toJSON (RecordModuleIFS range name) = kind' "RecordModuleIFS"
    [ "range"     .= range
    , "name"      .= name
    ]

instance ToJSON OpenShortHand where
  toJSON DoOpen   = String "DoOpen"
  toJSON DontOpen = String "DontOpen"

instance EncodeTCM Pragma where
instance ToJSON Pragma where
  toJSON pragma = case pragma of
    OptionsPragma range options -> kind' "OptionsPragma"
      [ "range"     .= range
      , "options"   .= options
      ]
    BuiltinPragma range entity name fixity -> kind' "BuiltinPragma"
      [ "range"     .= range
      , "entity"    .= entity
      , "name"      .= name
      , "fixity"    .= fixity
      ]
    RewritePragma range names -> kind' "RewritePragma"
      [ "range"     .= range
      , "names"      .= names
      ]
    CompiledDataPragma range name hd hcs -> kind' "CompiledDataPragma"
      [ "range"         .= range
      , "name"          .= name
      , "data"          .= hd
      , "constructors"  .= hcs
      ]
    CompiledTypePragma range name ht -> kind' "CompiledTypePragma"
      [ "range"         .= range
      , "name"          .= name
      , "type"          .= ht
      ]
    CompiledPragma range name hs -> kind' "CompiledPragma"
      [ "range"         .= range
      , "name"          .= name
      , "haskell"       .= hs
      ]
    CompiledExportPragma range name export -> kind' "CompiledExportPragma"
      [ "range"         .= range
      , "name"          .= name
      , "export"        .= export
      ]
    CompiledJSPragma range name js -> kind' "CompiledJSPragma"
      [ "range"         .= range
      , "name"          .= name
      , "js"            .= js
      ]
    CompiledUHCPragma range name uhc -> kind' "CompiledUHCPragma"
      [ "range"         .= range
      , "name"          .= name
      , "uhc"           .= uhc
      ]
    CompiledDataUHCPragma range name uhcd uhccs -> kind' "CompiledDataUHCPragma"
      [ "range"         .= range
      , "name"          .= name
      , "data"          .= uhcd
      , "constructors"  .= uhccs
      ]
    HaskellCodePragma range code -> kind' "HaskellCodePragma"
      [ "range"         .= range
      , "code"          .= code
      ]
    ForeignPragma range backend code -> kind' "ForeignPragma"
      [ "range"         .= range
      , "backend"       .= backend
      , "code"          .= code
      ]
    CompilePragma range backend name code -> kind' "CompilePragma"
      [ "range"         .= range
      , "backend"       .= backend
      , "name"          .= name
      , "code"          .= code
      ]
    StaticPragma range name -> kind' "StaticPragma"
      [ "range"         .= range
      , "name"          .= name
      ]
    InjectivePragma range name -> kind' "InjectivePragma"
      [ "range"         .= range
      , "name"          .= name
      ]
    InlinePragma range inline name -> kind' "InlinePragma"
      [ "range"         .= range
      , "inline"        .= inline
      , "name"          .= name
      ]
    ImportPragma range hsm -> kind' "ImportPragma"
      [ "range"         .= range
      , "module"        .= hsm
      ]
    ImportUHCPragma range uhcsm -> kind' "ImportUHCPragma"
      [ "range"         .= range
      , "module"        .= uhcsm
      ]
    ImpossiblePragma range -> kind' "ImpossiblePragma"
      [ "range"         .= range
      ]
    EtaPragma range name -> kind' "EtaPragma"
      [ "range"         .= range
      , "name"          .= name
      ]
    TerminationCheckPragma range name -> kind' "TerminationCheckPragma"
      [ "range"         .= range
      , "name"          .= name
      ]
    WarningOnUsage range name warning -> kind' "WarningOnUsage"
      [ "range"         .= range
      , "name"          .= name
      , "warning"       .= warning
      ]
    CatchallPragma range -> kind' "CatchallPragma"
      [ "range"         .= range
      ]
    DisplayPragma range pattern expr -> kind' "DisplayPragma"
      [ "range"         .= range
      , "pattern"       .= pattern
      , "expr"          .= expr
      ]
    NoPositivityCheckPragma range -> kind' "NoPositivityCheckPragma"
      [ "range"         .= range
      ]
    PolarityPragma range name occurrences -> kind' "PolarityPragma"
      [ "range"         .= range
      , "name"          .= name
      , "occurrences"   .= occurrences
      ]
    NoUniverseCheckPragma range -> kind' "NoUniverseCheckPragma"
      [ "range"         .= range
      ]

--------------------------------------------------------------------------------

instance EncodeTCM DeclarationWarning where
instance ToJSON DeclarationWarning where
  toJSON warning = case warning of
    EmptyAbstract range -> kind' "EmptyAbstract"
      [ "range"     .= range
      ]
    EmptyInstance range -> kind' "EmptyInstance"
      [ "range"     .= range
      ]
    EmptyMacro range -> kind' "EmptyMacro"
      [ "range"     .= range
      ]
    EmptyMutual range -> kind' "EmptyMutual"
      [ "range"     .= range
      ]
    EmptyPostulate range -> kind' "EmptyPostulate"
      [ "range"     .= range
      ]
    EmptyPrivate range -> kind' "EmptyPrivate"
      [ "range"     .= range
      ]
    InvalidCatchallPragma range -> kind' "InvalidCatchallPragma"
      [ "range"     .= range
      ]
    InvalidNoPositivityCheckPragma range -> kind' "InvalidNoPositivityCheckPragma"
      [ "range"     .= range
      ]
    InvalidNoUniverseCheckPragma range -> kind' "InvalidNoUniverseCheckPragma"
      [ "range"     .= range
      ]
    InvalidTerminationCheckPragma range -> kind' "InvalidTerminationCheckPragma"
      [ "range"     .= range
      ]
    MissingDefinitions names -> kind' "MissingDefinitions"
      [ "names"     .= names
      ]
    NotAllowedInMutual range name -> kind' "NotAllowedInMutual"
      [ "range"     .= range
      , "name"      .= name
      ]
    PolarityPragmasButNotPostulates names -> kind' "PolarityPragmasButNotPostulates"
      [ "names"     .= names
      ]
    PragmaNoTerminationCheck range -> kind' "PragmaNoTerminationCheck"
      [ "range"     .= range
      ]
    UnknownFixityInMixfixDecl names -> kind' "UnknownFixityInMixfixDecl"
      [ "names"     .= names
      ]
    UnknownNamesInFixityDecl names -> kind' "UnknownNamesInFixityDecl"
      [ "names"     .= names
      ]
    UnknownNamesInPolarityPragmas names -> kind' "UnknownNamesInPolarityPragmas"
      [ "names"     .= names
      ]
    UselessAbstract range -> kind' "UselessAbstract"
      [ "range"     .= range
      ]
    UselessInstance range -> kind' "UselessInstance"
      [ "range"     .= range
      ]
    UselessPrivate range -> kind' "UselessPrivate"
      [ "range"     .= range
      ]
