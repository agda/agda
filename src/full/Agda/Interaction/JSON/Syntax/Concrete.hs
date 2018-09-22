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
  toJSON (SyntaxBindingLambda range bindings value) = object
    [ "kind"      .= String "SyntaxBindingLambda"
    , "range"     .= range
    , "bindings"  .= bindings
    , "value"     .= value
    ]
  toJSON (Ordinary  value) = object
    [ "kind"      .= String "Ordinary"
    , "value"     .= value
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
    Ident name -> object
      [ "kind"      .= String "Ident"
      , "name"      .= name
      ]
    Lit literal -> object
      [ "kind"      .= String "Lit"
      , "literal"   .= literal
      ]
    QuestionMark range index -> object
      [ "kind"      .= String "QuestionMark"
      , "range"     .= range
      , "index"     .= index
      ]
    Underscore range name -> object
      [ "kind"      .= String "Underscore"
      , "range"     .= range
      , "name"      .= name
      ]
    RawApp range exprs -> object
      [ "kind"      .= String "RawApp"
      , "range"     .= range
      , "exprs"     .= exprs
      ]
    App range expr args -> object
      [ "kind"      .= String "App"
      , "range"     .= range
      , "expr"      .= expr
      , "args"      .= args
      ]
    OpApp range name names args -> object
      [ "kind"      .= String "OpApp"
      , "range"     .= range
      , "name"      .= name
      , "names"     .= names
      , "args"      .= args
      ]
    WithApp range expr exprs -> object
      [ "kind"      .= String "WithApp"
      , "range"     .= range
      , "expr"      .= expr
      , "exprs"     .= exprs
      ]
    HiddenArg range expr -> object
      [ "kind"      .= String "HiddenArg"
      , "range"     .= range
      , "expr"      .= expr
      ]
    InstanceArg range expr -> object
      [ "kind"      .= String "InstanceArg"
      , "range"     .= range
      , "expr"      .= expr
      ]
    Lam range bindings expr -> object
      [ "kind"      .= String "Lam"
      , "range"     .= range
      , "bindings"  .= bindings
      , "expr"      .= expr
      ]
    AbsurdLam range hiding -> object
      [ "kind"      .= String "AbsurdLam"
      , "range"     .= range
      , "hiding"    .= hiding
      ]
    ExtendedLam range clauses -> object
      [ "kind"      .= String "ExtendedLam"
      , "range"     .= range
      , "clauses"   .= clauses
      ]
    Fun range arg expr -> object
      [ "kind"      .= String "Fun"
      , "range"     .= range
      , "arg"       .= arg
      , "expr"      .= expr
      ]
    Pi telescope expr -> object
      [ "kind"      .= String "Pi"
      , "telescope" .= smashTel telescope
      , "expr"      .= expr
      ]
    Set range -> object
      [ "kind"      .= String "Set"
      , "range"     .= range
      ]
    Prop range -> object
      [ "kind"      .= String "Prop"
      , "range"     .= range
      ]
    SetN range level -> object
      [ "kind"      .= String "SetN"
      , "range"     .= range
      , "level"     .= level
      ]
    PropN range level -> object
      [ "kind"      .= String "PropN"
      , "range"     .= range
      , "level"     .= level
      ]
    Rec range assignments -> object
      [ "kind"        .= String "Rec"
      , "range"       .= range
      , "assignments" .= assignments
      ]
    RecUpdate range expr assignments -> object
      [ "kind"        .= String "RecUpdate"
      , "range"       .= range
      , "expr"        .= expr
      , "assignments" .= assignments
      ]
    Let range declarations expr -> object
      [ "kind"          .= String "Let"
      , "range"         .= range
      , "declarations"  .= declarations
      , "expr"          .= expr
      ]
    Paren range expr -> object
      [ "kind"      .= String "Paren"
      , "range"     .= range
      , "expr"      .= expr
      ]
    IdiomBrackets range expr -> object
      [ "kind"      .= String "IdiomBrackets"
      , "range"     .= range
      , "expr"      .= expr
      ]
    DoBlock range dostmts -> object
      [ "kind"      .= String "DoBlock"
      , "range"     .= range
      , "dostmts"   .= dostmts
      ]
    Absurd range -> object
      [ "kind"      .= String "Absurd"
      , "range"     .= range
      ]
    As range name expr -> object
      [ "kind"      .= String "As"
      , "range"     .= range
      , "name"      .= name
      , "expr"      .= expr
      ]
    Dot range expr -> object
      [ "kind"      .= String "Dot"
      , "range"     .= range
      , "expr"      .= expr
      ]
    ETel telescope -> object
      [ "kind"      .= String "ETel"
      , "telescope" .= telescope
      ]
    QuoteGoal range name expr -> object
      [ "kind"      .= String "QuoteGoal"
      , "range"     .= range
      , "name"      .= name
      , "expr"      .= expr
      ]
    QuoteContext range -> object
      [ "kind"      .= String "QuoteContext"
      , "range"     .= range
      ]
    Quote range -> object
      [ "kind"      .= String "Quote"
      , "range"     .= range
      ]
    QuoteTerm range -> object
      [ "kind"      .= String "QuoteTerm"
      , "range"     .= range
      ]
    Tactic range expr exprs -> object
      [ "kind"      .= String "Tactic"
      , "range"     .= range
      , "expr"      .= expr
      , "exprs"     .= exprs
      ]
    Unquote range -> object
      [ "kind"      .= String "Unquote"
      , "range"     .= range
      ]
    DontCare expr -> object
      [ "kind"      .= String "DontCare"
      , "expr"     .= expr
      ]
    Equal range expr1 expr2 -> object
      [ "kind"      .= String "Equal"
      , "range"     .= range
      , "expr1"     .= expr1
      , "expr2"     .= expr2
      ]
    Ellipsis range -> object
      [ "kind"      .= String "Ellipsis"
      , "range"     .= range
      ]
    Generalized range -> object
      [ "kind"      .= String "Generalized"
      , "expr"      .= expr
      ]

instance EncodeTCM Pattern where
instance ToJSON Pattern where
  toJSON pattern = case pattern of
    IdentP name -> object
      [ "kind"      .= String "IdentP"
      , "name"      .= name
      ]
    QuoteP range -> object
      [ "kind"      .= String "QuoteP"
      , "range"     .= range
      ]
    AppP pattern arg -> object
      [ "kind"      .= String "AppP"
      , "pattern"   .= pattern
      , "arg"       .= arg
      ]
    RawAppP range patterns -> object
      [ "kind"      .= String "RawAppP"
      , "range"     .= range
      , "patterns"  .= patterns
      ]
    OpAppP range name names args -> object
      [ "kind"      .= String "OpAppP"
      , "range"     .= range
      , "name"      .= name
      , "names"     .= names
      , "args"      .= args
      ]
    HiddenP range pattern -> object
      [ "kind"      .= String "HiddenP"
      , "range"     .= range
      , "pattern"   .= pattern
      ]
    InstanceP range pattern -> object
      [ "kind"      .= String "InstanceP"
      , "range"     .= range
      , "pattern"   .= pattern
      ]
    ParenP range pattern -> object
      [ "kind"      .= String "ParenP"
      , "range"     .= range
      , "pattern"   .= pattern
      ]
    WildP range -> object
      [ "kind"      .= String "WildP"
      , "range"     .= range
      ]
    AbsurdP range -> object
      [ "kind"      .= String "AbsurdP"
      , "range"     .= range
      ]
    AsP range name pattern -> object
      [ "kind"      .= String "AsP"
      , "range"     .= range
      , "name"      .= name
      , "pattern"   .= pattern
      ]
    DotP range expr -> object
      [ "kind"      .= String "DotP"
      , "range"     .= range
      , "expr"      .= expr
      ]
    LitP literal -> object
      [ "kind"      .= String "LitP"
      , "literal"   .= literal
      ]
    RecP range assignments -> object
      [ "kind"        .= String "RecP"
      , "range"       .= range
      , "assignments" .= assignments
      ]
    EqualP range pairs -> object
      [ "kind"      .= String "EqualP"
      , "range"     .= range
      , "pairs"     .= pairs
      ]
    EllipsisP range -> object
      [ "kind"      .= String "EllipsisP"
      , "range"     .= range
      ]
    WithP range pattern -> object
      [ "kind"      .= String "WithP"
      , "range"     .= range
      , "pattern"   .= pattern
      ]

instance ToJSON DoStmt where
  toJSON (DoBind range pattern expr clauses) = object
    [ "kind"      .= String "DoBind"
    , "range"     .= range
    , "pattern"   .= pattern
    , "expr"      .= expr
    , "clauses"   .= clauses
    ]
  toJSON (DoThen expr) = object
    [ "kind"      .= String "DoThen"
    , "expr"      .= expr
    ]
  toJSON (DoLet range declarations) = object
    [ "kind"          .= String "DoLet"
    , "range"         .= range
    , "declarations"  .= declarations
    ]

instance ToJSON a => ToJSON (LamBinding' a) where
  toJSON (DomainFree argInfo name) = object
    [ "kind"      .= String "DomainFree"
    , "argInfo"   .= argInfo
    , "name"      .= name
    ]
  toJSON (DomainFull value) = object
    [ "kind"      .= String "DomainFull"
    , "value"     .= value
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
  toJSON (TBind range bindings value) = object
    [ "kind"      .= String "TBind"
    , "range"     .= range
    , "bindings"  .= bindings
    , "value"     .= value
    ]
  toJSON (TLet range declarations) = object
    [ "kind"          .= String "TLet"
    , "range"         .= range
    , "declarations"  .= declarations
    ]

instance ToJSON LHS where
  toJSON (LHS pattern rewrites withExpr) = object
    [ "originalPattern" .= pattern
    , "rewriteEqn"      .= rewrites
    , "withExpr"        .= withExpr
    ]

instance ToJSON LHSCore where
  toJSON (LHSHead name patterns) = object
    [ "kind"            .= String "LHSHead"
    , "name"            .= name
    , "patterns"        .= patterns
    ]
  toJSON (LHSProj name patternsLeft focus patterns) = object
    [ "kind"            .= String "LHSProj"
    , "name"            .= name
    , "patternsLeft"     .= patternsLeft
    , "focus"           .= focus
    , "patterns"        .= patterns
    ]
  toJSON (LHSWith head withPatterns patterns) = object
    [ "kind"            .= String "LHSWith"
    , "head"            .= head
    , "withPatterns"    .= withPatterns
    , "patterns"        .= patterns
    ]

instance ToJSON a => ToJSON (RHS' a) where
  toJSON AbsurdRHS = object
    [ "kind"            .= String "AbsurdRHS"
    ]
  toJSON (RHS value) = object
    [ "kind"            .= String "RHS"
    , "value"           .= value
    ]

instance ToJSON a => ToJSON (WhereClause' a) where
  toJSON NoWhere = object
    [ "kind"            .= String "NoWhere"
    ]
  toJSON (AnyWhere declarations) = object
    [ "kind"            .= String "AnyWhere"
    , "declarations"    .= declarations
    ]
  toJSON (SomeWhere name access declarations) = object
    [ "kind"            .= String "SomeWhere"
    , "name"            .= name
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
    TypeSig argInfo name expr -> object
      [ "kind"            .= String "TypeSig"
      , "argInfo"         .= argInfo
      , "name"            .= name
      , "expr"            .= expr
      ]
    Generalize argInfo name expr -> object
      [ "kind"            .= String "Generalize"
      , "argInfo"         .= argInfo
      , "name"            .= name
      , "expr"            .= expr
      ]
    Field inst name arg -> object
      [ "kind"            .= String "Field"
      , "instance"        .= inst
      , "name"            .= name
      , "arg"             .= arg
      ]
    FunClause lhs rhs whereClause catchAll -> object
      [ "kind"            .= String "FunClause"
      , "LHS"             .= lhs
      , "RHS"             .= rhs
      , "whereClause"     .= whereClause
      , "catchAll"        .= catchAll
      ]
    DataSig range induction name bindings expr -> object
      [ "kind"            .= String "DataSig"
      , "range"           .= range
      , "induction"       .= induction
      , "name"            .= name
      , "bindings"        .= bindings
      , "expr"            .= expr
      ]
    Data range induction name bindings expr declarations -> object
      [ "kind"            .= String "Data"
      , "range"           .= range
      , "induction"       .= induction
      , "name"            .= name
      , "bindings"        .= bindings
      , "expr"            .= expr
      , "declarations"    .= declarations
      ]
    RecordSig range name bindings expr -> object
      [ "kind"            .= String "RecordSig"
      , "range"           .= range
      , "name"            .= name
      , "bindings"        .= bindings
      , "expr"            .= expr
      ]
    Record range name induction hasEta instancePairs bindings expr declarations
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
    Infix fixity names -> object
      [ "kind"            .= String "Field"
      , "fixity"          .= fixity
      , "names"           .= names
      ]
    Syntax name notation -> object
      [ "kind"            .= String "Syntax"
      , "name"            .= name
      , "notation"        .= notation
      ]
    PatternSyn range name args pattern -> object
      [ "kind"            .= String "PatternSyn"
      , "range"           .= range
      , "name"            .= name
      , "args"            .= args
      , "pattern"         .= pattern
      ]
    Mutual range declarations -> object
      [ "kind"            .= String "Mutual"
      , "range"           .= range
      , "declarations"    .= declarations
      ]
    Abstract range declarations -> object
      [ "kind"            .= String "Abstract"
      , "range"           .= range
      , "declarations"    .= declarations
      ]
    Private range origin declarations -> object
      [ "kind"            .= String "Private"
      , "range"           .= range
      , "origin"          .= origin
      , "declarations"    .= declarations
      ]
    InstanceB range declarations -> object
      [ "kind"            .= String "InstanceB"
      , "range"           .= range
      , "declarations"    .= declarations
      ]
    Macro range declarations -> object
      [ "kind"            .= String "Macro"
      , "range"           .= range
      , "declarations"    .= declarations
      ]
    Postulate range declarations -> object
      [ "kind"            .= String "Postulate"
      , "range"           .= range
      , "declarations"    .= declarations
      ]
    Primitive range declarations -> object
      [ "kind"            .= String "Primitive"
      , "range"           .= range
      , "declarations"    .= declarations
      ]
    Open range name importDirective -> object
      [ "kind"            .= String "Primitive"
      , "range"           .= range
      , "name"            .= name
      , "importDirective" .= importDirective
      ]
    Import range name asName openShortHand importDirective -> object
      [ "kind"            .= String "Import"
      , "range"           .= range
      , "name"            .= name
      , "asName"          .= asName
      , "openShortHand"   .= openShortHand
      , "importDirective" .= importDirective
      ]
    ModuleMacro range name moduleApp openShortHand importDirective -> object
      [ "kind"            .= String "ModuleMacro"
      , "range"           .= range
      , "name"            .= name
      , "moduleApp"       .= moduleApp
      , "openShortHand"   .= openShortHand
      , "importDirective" .= importDirective
      ]
    Module range name bindings declarations -> object
      [ "kind"            .= String "Module"
      , "range"           .= range
      , "name"            .= name
      , "bindings"        .= bindings
      , "declarations"    .= declarations
      ]
    UnquoteDecl range names expr -> object
      [ "kind"            .= String "UnquoteDecl"
      , "range"           .= range
      , "names"           .= names
      , "expr"            .= expr
      ]
    UnquoteDef range names expr -> object
      [ "kind"            .= String "UnquoteDef"
      , "range"           .= range
      , "names"           .= names
      , "expr"            .= expr
      ]
    Pragma pragma -> object
      [ "kind"            .= String "Pragma"
      , "pragma"          .= pragma
      ]


instance ToJSON ModuleApplication where
  toJSON (SectionApp range bindings expr) = object
    [ "kind"      .= String "SectionApp"
    , "range"     .= range
    , "bindings"  .= bindings
    , "expr"      .= expr
    ]
  toJSON (RecordModuleIFS range name) = object
    [ "kind"      .= String "RecordModuleIFS"
    , "range"     .= range
    , "name"      .= name
    ]

instance ToJSON OpenShortHand where
  toJSON DoOpen   = String "DoOpen"
  toJSON DontOpen = String "DontOpen"

instance EncodeTCM Pragma where
instance ToJSON Pragma where
  toJSON pragma = case pragma of
    OptionsPragma range options -> object
      [ "kind"      .= String "OptionsPragma"
      , "range"     .= range
      , "options"   .= options
      ]
    BuiltinPragma range entity name fixity -> object
      [ "kind"      .= String "BuiltinPragma"
      , "range"     .= range
      , "entity"    .= entity
      , "name"      .= name
      , "fixity"    .= fixity
      ]
    RewritePragma range names -> object
      [ "kind"      .= String "RewritePragma"
      , "range"     .= range
      , "names"      .= names
      ]
    CompiledDataPragma range name hd hcs -> object
      [ "kind"          .= String "CompiledDataPragma"
      , "range"         .= range
      , "name"          .= name
      , "data"          .= hd
      , "constructors"  .= hcs
      ]
    CompiledTypePragma range name ht -> object
      [ "kind"          .= String "CompiledTypePragma"
      , "range"         .= range
      , "name"          .= name
      , "type"          .= ht
      ]
    CompiledPragma range name hs -> object
      [ "kind"          .= String "CompiledPragma"
      , "range"         .= range
      , "name"          .= name
      , "haskell"       .= hs
      ]
    CompiledExportPragma range name export -> object
      [ "kind"          .= String "CompiledExportPragma"
      , "range"         .= range
      , "name"          .= name
      , "export"        .= export
      ]
    CompiledJSPragma range name js -> object
      [ "kind"          .= String "CompiledJSPragma"
      , "range"         .= range
      , "name"          .= name
      , "js"            .= js
      ]
    CompiledUHCPragma range name uhc -> object
      [ "kind"          .= String "CompiledUHCPragma"
      , "range"         .= range
      , "name"          .= name
      , "uhc"           .= uhc
      ]
    CompiledDataUHCPragma range name uhcd uhccs -> object
      [ "kind"          .= String "CompiledDataUHCPragma"
      , "range"         .= range
      , "name"          .= name
      , "data"          .= uhcd
      , "constructors"  .= uhccs
      ]
    HaskellCodePragma range code -> object
      [ "kind"          .= String "HaskellCodePragma"
      , "range"         .= range
      , "code"          .= code
      ]
    ForeignPragma range backend code -> object
      [ "kind"          .= String "ForeignPragma"
      , "range"         .= range
      , "backend"       .= backend
      , "code"          .= code
      ]
    CompilePragma range backend name code -> object
      [ "kind"          .= String "CompilePragma"
      , "range"         .= range
      , "backend"       .= backend
      , "name"          .= name
      , "code"          .= code
      ]
    StaticPragma range name -> object
      [ "kind"          .= String "StaticPragma"
      , "range"         .= range
      , "name"          .= name
      ]
    InjectivePragma range name -> object
      [ "kind"          .= String "InjectivePragma"
      , "range"         .= range
      , "name"          .= name
      ]
    InlinePragma range inline name -> object
      [ "kind"          .= String "InlinePragma"
      , "range"         .= range
      , "inline"        .= inline
      , "name"          .= name
      ]
    ImportPragma range hsm -> object
      [ "kind"          .= String "ImportPragma"
      , "range"         .= range
      , "module"        .= hsm
      ]
    ImportUHCPragma range uhcsm -> object
      [ "kind"          .= String "ImportUHCPragma"
      , "range"         .= range
      , "module"        .= uhcsm
      ]
    ImpossiblePragma range -> object
      [ "kind"          .= String "ImpossiblePragma"
      , "range"         .= range
      ]
    EtaPragma range name -> object
      [ "kind"          .= String "EtaPragma"
      , "range"         .= range
      , "name"          .= name
      ]
    TerminationCheckPragma range name -> object
      [ "kind"          .= String "TerminationCheckPragma"
      , "range"         .= range
      , "name"          .= name
      ]
    WarningOnUsage range name warning -> object
      [ "kind"          .= String "WarningOnUsage"
      , "range"         .= range
      , "name"          .= name
      , "warning"       .= warning
      ]
    CatchallPragma range -> object
      [ "kind"          .= String "CatchallPragma"
      , "range"         .= range
      ]
    DisplayPragma range pattern expr -> object
      [ "kind"          .= String "DisplayPragma"
      , "range"         .= range
      , "pattern"       .= pattern
      , "expr"          .= expr
      ]
    NoPositivityCheckPragma range -> object
      [ "kind"          .= String "NoPositivityCheckPragma"
      , "range"         .= range
      ]
    PolarityPragma range name occurrences -> object
      [ "kind"          .= String "PolarityPragma"
      , "range"         .= range
      , "name"          .= name
      , "occurrences"   .= occurrences
      ]
    NoUniverseCheckPragma range -> object
      [ "kind"          .= String "NoUniverseCheckPragma"
      , "range"         .= range
      ]

--------------------------------------------------------------------------------

instance EncodeTCM DeclarationWarning where
instance ToJSON DeclarationWarning where
  toJSON warning = case warning of
    EmptyAbstract range -> object
      [ "kind"      .= String "EmptyAbstract"
      , "range"     .= range
      ]
    EmptyInstance range -> object
      [ "kind"      .= String "EmptyInstance"
      , "range"     .= range
      ]
    EmptyMacro range -> object
      [ "kind"      .= String "EmptyMacro"
      , "range"     .= range
      ]
    EmptyMutual range -> object
      [ "kind"      .= String "EmptyMutual"
      , "range"     .= range
      ]
    EmptyPostulate range -> object
      [ "kind"      .= String "EmptyPostulate"
      , "range"     .= range
      ]
    EmptyPrivate range -> object
      [ "kind"      .= String "EmptyPrivate"
      , "range"     .= range
      ]
    InvalidCatchallPragma range -> object
      [ "kind"      .= String "InvalidCatchallPragma"
      , "range"     .= range
      ]
    InvalidNoPositivityCheckPragma range -> object
      [ "kind"      .= String "InvalidNoPositivityCheckPragma"
      , "range"     .= range
      ]
    InvalidNoUniverseCheckPragma range -> object
      [ "kind"      .= String "InvalidNoUniverseCheckPragma"
      , "range"     .= range
      ]
    InvalidTerminationCheckPragma range -> object
      [ "kind"      .= String "InvalidTerminationCheckPragma"
      , "range"     .= range
      ]
    MissingDefinitions names -> object
      [ "kind"      .= String "MissingDefinitions"
      , "names"     .= names
      ]
    NotAllowedInMutual range name -> object
      [ "kind"      .= String "NotAllowedInMutual"
      , "range"     .= range
      , "name"      .= name
      ]
    PolarityPragmasButNotPostulates names -> object
      [ "kind"      .= String "PolarityPragmasButNotPostulates"
      , "names"     .= names
      ]
    PragmaNoTerminationCheck range -> object
      [ "kind"      .= String "PragmaNoTerminationCheck"
      , "range"     .= range
      ]
    UnknownFixityInMixfixDecl names -> object
      [ "kind"      .= String "UnknownFixityInMixfixDecl"
      , "names"     .= names
      ]
    UnknownNamesInFixityDecl names -> object
      [ "kind"      .= String "UnknownNamesInFixityDecl"
      , "names"     .= names
      ]
    UnknownNamesInPolarityPragmas names -> object
      [ "kind"      .= String "UnknownNamesInPolarityPragmas"
      , "names"     .= names
      ]
    UselessAbstract range -> object
      [ "kind"      .= String "UselessAbstract"
      , "range"     .= range
      ]
    UselessInstance range -> object
      [ "kind"      .= String "UselessInstance"
      , "range"     .= range
      ]
    UselessPrivate range -> object
      [ "kind"      .= String "UselessPrivate"
      , "range"     .= range
      ]
