{-# LANGUAGE CPP, DeriveDataTypeable, DeriveFunctor, DeriveTraversable, DeriveFoldable #-}

{-| The concrete syntax is a raw representation of the program text
    without any desugaring at all.  This is what the parser produces.
    The idea is that if we figure out how to keep the concrete syntax
    around, it can be printed exactly as the user wrote it.
-}
module Agda.Syntax.Concrete
    ( -- * Expressions
      Expr(..)
    , OpApp(..), fromOrdinary
    , module Agda.Syntax.Concrete.Name
    , appView, AppView(..)
      -- * Bindings
    , LamBinding(..)
    , TypedBindings(..)
    , TypedBinding(..)
    , BoundName(..), mkBoundName_
    , Telescope -- (..)
      -- * Declarations
    , Declaration(..)
    , ModuleApplication(..)
    , TypeSignature
    , Constructor
    , ImportDirective(..), UsingOrHiding(..), ImportedName(..)
    , Renaming(..), AsName(..)
    , defaultImportDir
    , OpenShortHand(..), RewriteEqn, WithExpr
    , LHS(..), Pattern(..), LHSCore(..)
    , RHS(..), WhereClause(..)
    , Pragma(..)
    , Module
    , ThingWithFixity(..)
    , topLevelModuleName
    -- * Pattern tools
    , patternHead, patternNames
    )
    where

import Data.Typeable (Typeable)
import Data.Foldable hiding (concatMap)
import Data.Traversable
import Agda.Syntax.Position
import Agda.Syntax.Common
import Agda.Syntax.Fixity
import Agda.Syntax.Notation
import Agda.Syntax.Literal

import Agda.Syntax.Concrete.Name

import Agda.Utils.Impossible
#include "../undefined.h"

data OpApp e
        = SyntaxBindingLambda !Range [LamBinding] e -- ^ an abstraction inside a special syntax declaration (see Issue 358 why we introduce this).
        | Ordinary e
    deriving (Typeable, Functor)

fromOrdinary :: e -> OpApp e -> e
fromOrdinary d (Ordinary e) = e
fromOrdinary d _            = d

-- | Concrete expressions. Should represent exactly what the user wrote.
data Expr
	= Ident QName			       -- ^ ex: @x@
	| Lit Literal			       -- ^ ex: @1@ or @\"foo\"@
	| QuestionMark !Range (Maybe Nat)      -- ^ ex: @?@ or @{! ... !}@
	| Underscore !Range (Maybe String)     -- ^ ex: @_@ or @_A_5@
	| RawApp !Range [Expr]		       -- ^ before parsing operators
	| App !Range Expr (NamedArg Expr)      -- ^ ex: @e e@, @e {e}@, or @e {x = e}@
	| OpApp !Range QName [OpApp Expr]      -- ^ ex: @e + e@
        | WithApp !Range Expr [Expr]           -- ^ ex: @e | e1 | .. | en@
	| HiddenArg !Range (Named String Expr) -- ^ ex: @{e}@ or @{x=e}@
	| InstanceArg !Range (Named String Expr) -- ^ ex: @{{e}}@ or @{{x=e}}@
	| Lam !Range [LamBinding] Expr	       -- ^ ex: @\\x {y} -> e@ or @\\(x:A){y:B} -> e@
        | AbsurdLam !Range Hiding              -- ^ ex: @\\ ()@
        | ExtendedLam !Range [(LHS,RHS,WhereClause)]       -- ^ ex: @\\ { p11 .. p1a -> e1 ; .. ; pn1 .. pnz -> en }@
	| Fun !Range Expr Expr                 -- ^ ex: @e -> e@ or @.e -> e@ (NYI: @{e} -> e@)
	| Pi Telescope Expr		       -- ^ ex: @(xs:e) -> e@ or @{xs:e} -> e@
	| Set !Range			       -- ^ ex: @Set@
	| Prop !Range			       -- ^ ex: @Prop@
	| SetN !Range Integer                  -- ^ ex: @Set0, Set1, ..@
	| Rec !Range [(Name, Expr)]	       -- ^ ex: @record {x = a; y = b}@
	| RecUpdate !Range Expr [(Name, Expr)] -- ^ ex: @record e {x = a; y = b}@
	| Let !Range [Declaration] Expr	       -- ^ ex: @let Ds in e@
	| Paren !Range Expr		       -- ^ ex: @(e)@
	| Absurd !Range			       -- ^ ex: @()@ or @{}@, only in patterns
	| As !Range Name Expr		       -- ^ ex: @x\@p@, only in patterns
	| Dot !Range Expr		       -- ^ ex: @.p@, only in patterns
        | ETel Telescope                       -- ^ only used for printing telescopes
        | QuoteGoal !Range Name Expr           -- ^ ex: @quoteGoal x in e@
        | Quote !Range                         -- ^ ex: @quote@, should be applied to a name
        | QuoteTerm !Range                     -- ^ ex: @quoteTerm@, should be applied to a term
        | Unquote !Range                       -- ^ ex: @unquote@, should be applied to a term of type @Term@
        | DontCare Expr                        -- ^ to print irrelevant things
    deriving (Typeable)


-- | Concrete patterns. No literals in patterns at the moment.
data Pattern
	= IdentP QName                            -- ^ @c@ or @x@
	| AppP Pattern (NamedArg Pattern)         -- ^ @p p'@ or @p {x = p'}@
	| RawAppP !Range [Pattern]                -- ^ @p1..pn@ before parsing operators
	| OpAppP !Range QName [Pattern]           -- ^ eg: @p => p'@ for operator @_=>_@
	| HiddenP !Range (Named String Pattern)   -- ^ @{p}@ or @{x = p}@
	| InstanceP !Range (Named String Pattern) -- ^ @{{p}}@ or @{{x = p}}@
	| ParenP !Range Pattern                   -- ^ @(p)@
	| WildP !Range                            -- ^ @_@
	| AbsurdP !Range                          -- ^ @()@
	| AsP !Range Name Pattern                 -- ^ @x\@p@ unused
	| DotP !Range Expr                        -- ^ @.e@
	| LitP Literal                            -- ^ @0@, @1@, etc.
    deriving (Typeable)


-- | A lambda binding is either domain free or typed.
data LamBinding
	= DomainFree Hiding Relevance BoundName -- ^ . @x@ or @{x}@ or @.x@ or @.{x}@ or @{.x}@
	| DomainFull TypedBindings              -- ^ . @(xs : e)@ or @{xs : e}@
    deriving (Typeable)


-- | A sequence of typed bindings with hiding information. Appears in dependent
--   function spaces, typed lambdas, and telescopes.
data TypedBindings = TypedBindings !Range (Arg TypedBinding)
	-- ^ . @(xs : e)@ or @{xs : e}@
    deriving (Typeable)


data BoundName = BName { boundName   :: Name
                       , bnameFixity :: Fixity'
                       }
    deriving (Typeable)

mkBoundName_ :: Name -> BoundName
mkBoundName_ x = BName x defaultFixity'

-- | A typed binding.
data TypedBinding
	= TBind !Range [BoundName] Expr   -- Binding @x1,..,xn:A@
	| TNoBind Expr		    -- No binding @A@, equivalent to @_ : A@.
    deriving (Typeable)


-- | A telescope is a sequence of typed bindings. Bound variables are in scope
--   in later types.
type Telescope = [TypedBindings]

{-| Left hand sides can be written in infix style. For example:

    > n + suc m = suc (n + m)
    > (f ∘ g) x = f (g x)

   We use fixity information to see which name is actually defined.
-}
data LHS = LHS { lhsOriginalPattern :: Pattern       -- ^ @f ps@
               , lhsWithPattern     :: [Pattern]     -- ^ @| p@ (many)
               , lhsRewriteEqn      :: [RewriteEqn]  -- ^ @rewrite e@ (many)
               , lhsWithExpr        :: [WithExpr]    -- ^ @with e@ (many)
               }
         -- ^ original pattern, with-patterns, rewrite equations and with-expressions
         | Ellipsis Range [Pattern] [RewriteEqn] [WithExpr]
         -- ^ new with-patterns, rewrite equations and with-expressions
  deriving (Typeable)

type RewriteEqn = Expr
type WithExpr   = Expr

-- | Processed (scope-checked) intermediate form of the core @f ps@ of 'LHS'.
--   Corresponds to 'lhsOriginalPattern'.
data LHSCore
  = LHSHead  { lhsDefName  :: Name                -- ^ @f@
             , lhsPats     :: [NamedArg Pattern]  -- ^ @ps@
             }
  | LHSProj  { lhsDestructor :: QName      -- ^ record projection identifier
             , lhsPatsLeft   :: [NamedArg Pattern]  -- ^ side patterns
             , lhsFocus      :: NamedArg LHSCore    -- ^ main branch
             , lhsPatsRight  :: [NamedArg Pattern]  -- ^ side patterns
             }
  deriving (Typeable)

{- TRASH
lhsCoreToPattern :: LHSCore -> Pattern
lhsCoreToPattern (LHSHead f args) = OpAppP (fuseRange f args) (unqualify f) args
lhsCoreToPattern (LHSProj d ps1 lhscore ps2) = OpAppP (fuseRange d ps) (unqualify) ps
  where p = lhsCoreToPattern lhscore
        ps = ps1 ++ p : ps2
-}

data RHS = AbsurdRHS
	 | RHS Expr
    deriving (Typeable)

data WhereClause = NoWhere | AnyWhere [Declaration] | SomeWhere Name [Declaration]
  deriving (Typeable)


-- | The things you are allowed to say when you shuffle names between name
--   spaces (i.e. in @import@, @namespace@, or @open@ declarations).
data ImportDirective
	= ImportDirective
	    { importDirRange	:: !Range
	    , usingOrHiding	:: UsingOrHiding
	    , renaming		:: [Renaming]
	    , publicOpen	:: Bool	-- ^ Only for @open@. Exports the opened names from the current module.
	    }
    deriving (Typeable)

-- | Default is directive is @private@ (use everything, but do not export).
defaultImportDir :: ImportDirective
defaultImportDir = ImportDirective noRange (Hiding []) [] False

data UsingOrHiding
	= Hiding [ImportedName]
	| Using  [ImportedName]
    deriving (Typeable)

-- | An imported name can be a module or a defined name
data ImportedName = ImportedModule  { importedName :: Name }
		  | ImportedName    { importedName :: Name }
    deriving (Typeable, Eq, Ord)

instance Show ImportedName where
    show (ImportedModule x) = "module " ++ show x
    show (ImportedName   x) = show x

data Renaming = Renaming { renFrom    :: ImportedName
                           -- ^ Rename from this name.
                         , renTo      :: Name
                           -- ^ To this one.
                         , renToRange :: Range
                           -- ^ The range of the \"to\" keyword. Retained
                           --   for highlighting purposes.
                         }
    deriving (Typeable)

data AsName = AsName { asName  :: Name
                       -- ^ The \"as\" name.
                     , asRange :: Range
                       -- ^ The range of the \"as\" keyword. Retained
                       --   for highlighting purposes.
                     }
    deriving (Typeable, Show)

{--------------------------------------------------------------------------
    Declarations
 --------------------------------------------------------------------------}

-- | Just type signatures.
type TypeSignature   = Declaration

-- | A data constructor declaration is just a type signature.
type Constructor = TypeSignature

{-| The representation type of a declaration. The comments indicate
    which type in the intended family the constructor targets.
-}

data Declaration
	= TypeSig Relevance Name Expr -- ^ Axioms and functions can be irrelevant.
        | Field Name (Arg Expr) -- ^ Record field, can be hidden and/or irrelevant.
	| FunClause LHS RHS WhereClause
	| DataSig     !Range Induction Name [LamBinding] Expr -- ^ lone data signature in mutual block
	| Data        !Range Induction Name [LamBinding] (Maybe Expr) [Constructor]
	| RecordSig   !Range Name [LamBinding] Expr -- ^ lone record signature in mutual block
	| Record      !Range Name (Maybe Induction) (Maybe Name) [LamBinding] (Maybe Expr) [Declaration]
          -- ^ The optional name is a name for the record constructor.
	| Infix Fixity [Name]
        | Syntax      Name Notation -- ^ notation declaration for a name
        | PatternSyn  !Range Name [Name] Pattern
	| Mutual      !Range [Declaration]
	| Abstract    !Range [Declaration]
	| Private     !Range [Declaration]
	| Postulate   !Range [TypeSignature]
	| Primitive   !Range [TypeSignature]
	| Open        !Range QName ImportDirective
	| Import      !Range QName (Maybe AsName) OpenShortHand ImportDirective
	| ModuleMacro !Range  Name ModuleApplication OpenShortHand ImportDirective
	| Module      !Range QName [TypedBindings] [Declaration]
	| Pragma      Pragma
    deriving (Typeable)

data ModuleApplication = SectionApp Range [TypedBindings] Expr
                       | RecordModuleIFS Range QName
    deriving (Typeable)

data OpenShortHand = DoOpen | DontOpen
    deriving (Typeable, Show)

-- Pragmas ----------------------------------------------------------------

data Pragma = OptionsPragma     !Range [String]
	    | BuiltinPragma     !Range String Expr
            | CompiledDataPragma !Range QName String [String]
            | CompiledTypePragma !Range QName String
            | CompiledPragma    !Range QName String
            | CompiledEpicPragma !Range QName String
            | CompiledJSPragma  !Range QName String
            | StaticPragma      !Range QName
            | ImportPragma      !Range String
              -- ^ Invariant: The string must be a valid Haskell
              -- module name.
            | ImpossiblePragma !Range
            | EtaPragma !Range QName
            | NoTerminationCheckPragma !Range
    deriving (Typeable)

---------------------------------------------------------------------------

-- | Modules: Top-level pragmas plus other top-level declarations.

type Module = ([Pragma], [Declaration])

-- | Computes the top-level module name.
--
-- Precondition: The 'Module' has to be well-formed.

topLevelModuleName :: Module -> TopLevelModuleName
topLevelModuleName (_, []) = __IMPOSSIBLE__
topLevelModuleName (_, ds) = case last ds of
  Module _ n _ _ -> toTopLevelModuleName n
  _              -> __IMPOSSIBLE__

{--------------------------------------------------------------------------
    Views
 --------------------------------------------------------------------------}

-- | The 'Expr' is not an application.
data AppView = AppView Expr [NamedArg Expr]

appView :: Expr -> AppView
appView (App r e1 e2) = vApp (appView e1) e2
    where
	vApp (AppView e es) arg = AppView e (es ++ [arg])
appView (RawApp _ (e:es)) = AppView e $ map arg es
    where
	arg (HiddenArg   _ e) = Arg Hidden    Relevant e
	arg (InstanceArg _ e) = Arg Instance  Relevant e
	arg e		      = Arg NotHidden Relevant (unnamed e)
appView e = AppView e []

{--------------------------------------------------------------------------
    Patterns
 --------------------------------------------------------------------------}

-- | Get the leftmost symbol in a pattern.
patternHead :: Pattern -> Maybe Name
patternHead p =
  case p of
    IdentP x             -> return $ unqualify x
    AppP p p'            -> patternHead p
    RawAppP _ []         -> __IMPOSSIBLE__
    RawAppP _ (p:_)      -> patternHead p
    OpAppP _ name ps     -> return $ unqualify name
    HiddenP _ (namedPat) -> patternHead (namedThing namedPat)
    ParenP _ p           -> patternHead p
    WildP _              -> Nothing
    AbsurdP _            -> Nothing
    AsP _ x p            -> patternHead p
    DotP{}               -> Nothing
    LitP (LitQName _ x)  -> Nothing -- return $ unqualify x -- does not compile
    LitP _               -> Nothing
    InstanceP _ (namedPat) -> patternHead (namedThing namedPat)


-- | Get all the identifiers in a pattern in left-to-right order.
patternNames :: Pattern -> [Name]
patternNames p =
  case p of
    IdentP x             -> [unqualify x]
    AppP p p'            -> concatMap patternNames [p, namedThing $ unArg p']
    RawAppP _ ps         -> concatMap patternNames  ps
    OpAppP _ name ps     -> unqualify name : concatMap patternNames ps
    HiddenP _ (namedPat) -> patternNames (namedThing namedPat)
    ParenP _ p           -> patternNames p
    WildP _              -> []
    AbsurdP _            -> []
    AsP _ x p            -> patternNames p
    DotP{}               -> []
    LitP _               -> []
    InstanceP _ (namedPat) -> patternNames (namedThing namedPat)

{--------------------------------------------------------------------------
    Instances
 --------------------------------------------------------------------------}

instance HasRange e => HasRange (OpApp e) where
    getRange e = case e of
        Ordinary e -> getRange e
        SyntaxBindingLambda r _ _ -> r

instance HasRange Expr where
    getRange e =
	case e of
	    Ident x		-> getRange x
	    Lit x		-> getRange x
	    QuestionMark r _	-> r
	    Underscore r _	-> r
	    App r _ _		-> r
	    RawApp r _		-> r
	    OpApp r _ _		-> r
            WithApp r _ _       -> r
	    Lam r _ _		-> r
            AbsurdLam r _       -> r
            ExtendedLam r _       -> r
	    Fun r _ _		-> r
	    Pi b e		-> fuseRange b e
	    Set r		-> r
	    Prop r		-> r
	    SetN r _		-> r
	    Let r _ _		-> r
	    Paren r _		-> r
	    As r _ _		-> r
	    Dot r _		-> r
	    Absurd r		-> r
	    HiddenArg r _	-> r
	    InstanceArg r _	-> r
	    Rec r _		-> r
	    RecUpdate r _ _	-> r
            ETel tel            -> getRange tel
            QuoteGoal r _ _     -> r
            Quote r             -> r
            QuoteTerm r         -> r
            Unquote r           -> r
            DontCare{}          -> noRange

-- instance HasRange Telescope where
--     getRange (TeleBind bs) = getRange bs
--     getRange (TeleFun x y) = fuseRange x y

instance HasRange TypedBindings where
    getRange (TypedBindings r _) = r

instance HasRange TypedBinding where
    getRange (TBind r _ _) = r
    getRange (TNoBind e)   = getRange e

instance HasRange LamBinding where
    getRange (DomainFree _ _ x)	= getRange x
    getRange (DomainFull b)	= getRange b

instance HasRange BoundName where
  getRange = getRange . boundName

instance HasRange WhereClause where
  getRange  NoWhere	    = noRange
  getRange (AnyWhere ds)    = getRange ds
  getRange (SomeWhere _ ds) = getRange ds

instance HasRange ModuleApplication where
  getRange (SectionApp r _ _) = r
  getRange (RecordModuleIFS r _) = r

instance HasRange Declaration where
    getRange (TypeSig _ x t)	       = fuseRange x t
    getRange (Field x t)               = fuseRange x t
    getRange (FunClause lhs rhs wh)    = fuseRange lhs rhs `fuseRange` wh
    getRange (DataSig r _ _ _ _)       = r
    getRange (Data r _ _ _ _ _)	       = r
    getRange (RecordSig r _ _ _)       = r
    getRange (Record r _ _ _ _ _ _)    = r
    getRange (Mutual r _)	       = r
    getRange (Abstract r _)	       = r
    getRange (Open r _ _)	       = r
    getRange (ModuleMacro r _ _ _ _)   = r
    getRange (Import r _ _ _ _)	       = r
    getRange (Private r _)	       = r
    getRange (Postulate r _)	       = r
    getRange (Primitive r _)	       = r
    getRange (Module r _ _ _)	       = r
    getRange (Infix f _)	       = getRange f
    getRange (Syntax n _)              = getRange n
    getRange (PatternSyn r _ _ _)      = r
    getRange (Pragma p)		       = getRange p

instance HasRange LHS where
  getRange (LHS p ps eqns ws) = fuseRange p (fuseRange ps (eqns ++ ws))
  getRange (Ellipsis r _ _ _) = r

instance HasRange LHSCore where
  getRange (LHSHead f ps) = fuseRange f ps
  getRange (LHSProj d ps1 lhscore ps2) = d `fuseRange` ps1 `fuseRange` lhscore `fuseRange` ps2

instance HasRange RHS where
    getRange AbsurdRHS = noRange
    getRange (RHS e)   = getRange e

instance HasRange Pragma where
    getRange (OptionsPragma r _)          = r
    getRange (BuiltinPragma r _ _)        = r
    getRange (CompiledDataPragma r _ _ _) = r
    getRange (CompiledTypePragma r _ _)   = r
    getRange (CompiledPragma r _ _)       = r
    getRange (CompiledEpicPragma r _ _)   = r
    getRange (CompiledJSPragma r _ _)     = r
    getRange (StaticPragma r _)           = r
    getRange (ImportPragma r _)           = r
    getRange (ImpossiblePragma r)         = r
    getRange (EtaPragma r _)              = r
    getRange (NoTerminationCheckPragma r) = r

instance HasRange UsingOrHiding where
    getRange (Using xs)	    = getRange xs
    getRange (Hiding xs)    = getRange xs

instance HasRange ImportDirective where
    getRange = importDirRange

instance HasRange ImportedName where
    getRange (ImportedName x)	= getRange x
    getRange (ImportedModule x)	= getRange x

instance HasRange Renaming where
  getRange r = getRange (renFrom r, renTo r)

instance HasRange AsName where
  getRange a = getRange (asRange a, asName a)

instance HasRange Pattern where
    getRange (IdentP x)		= getRange x
    getRange (AppP p q)		= fuseRange p q
    getRange (OpAppP r _ _)	= r
    getRange (RawAppP r _)	= r
    getRange (ParenP r _)	= r
    getRange (WildP r)		= r
    getRange (AsP r _ _)	= r
    getRange (AbsurdP r)	= r
    getRange (LitP l)		= getRange l
    getRange (HiddenP r _)	= r
    getRange (InstanceP r _)	= r
    getRange (DotP r _)		= r

instance KillRange AsName where
  killRange (AsName n _) = killRange1 (flip AsName noRange) n

instance KillRange BoundName where
  killRange (BName n f) = killRange2 BName n f

instance KillRange Declaration where
  killRange (TypeSig r n e)         = killRange2 (TypeSig r) n e
  killRange (Field n a)             = killRange2 Field n a
  killRange (FunClause l r w)       = killRange3 FunClause l r w
  killRange (DataSig _ i n l e)     = killRange4 (DataSig noRange) i n l e
  killRange (Data _ i n l e c)      = killRange4 (Data noRange i) n l e c
  killRange (RecordSig _ n l e)     = killRange3 (RecordSig noRange) n l e
  killRange (Record _ n mi mn k e d)= killRange6 (Record noRange) n mi mn k e d
  killRange (Infix f n)             = killRange2 Infix f n
  killRange (Syntax n no)           = killRange1 (\n -> Syntax n no) n
  killRange (PatternSyn _ n ns p)   = killRange3 (PatternSyn noRange) n ns p
  killRange (Mutual _ d)            = killRange1 (Mutual noRange) d
  killRange (Abstract _ d)          = killRange1 (Abstract noRange) d
  killRange (Private _ d)           = killRange1 (Private noRange) d
  killRange (Postulate _ t)         = killRange1 (Postulate noRange) t
  killRange (Primitive _ t)         = killRange1 (Primitive noRange) t
  killRange (Open _ q i)            = killRange2 (Open noRange) q i
  killRange (Import _ q a o i)      = killRange3 (\q a -> Import noRange q a o) q a i
  killRange (ModuleMacro _ n m o i) = killRange3 (\n m -> ModuleMacro noRange n m o) n m i
  killRange (Module _ q t d)        = killRange3 (Module noRange) q t d
  killRange (Pragma p)              = killRange1 Pragma p

instance KillRange Expr where
  killRange (Ident q)           = killRange1 Ident q
  killRange (Lit l)             = killRange1 Lit l
  killRange (QuestionMark _ n)  = QuestionMark noRange n
  killRange (Underscore _ n)    = Underscore noRange n
  killRange (RawApp _ e)        = killRange1 (RawApp noRange) e
  killRange (App _ e a)         = killRange2 (App noRange) e a
  killRange (OpApp _ n o)       = killRange2 (OpApp noRange) n o
  killRange (WithApp _ e es)    = killRange2 (WithApp noRange) e es
  killRange (HiddenArg _ n)     = killRange1 (HiddenArg noRange) n
  killRange (InstanceArg _ n)   = killRange1 (InstanceArg noRange) n
  killRange (Lam _ l e)         = killRange2 (Lam noRange) l e
  killRange (AbsurdLam _ h)     = killRange1 (AbsurdLam noRange) h
  killRange (ExtendedLam _ lrw) = killRange1 (ExtendedLam noRange) lrw
  killRange (Fun _ e1 e2)       = killRange2 (Fun noRange) e1 e2
  killRange (Pi t e)            = killRange2 Pi t e
  killRange (Set _)             = Set noRange
  killRange (Prop _)            = Prop noRange
  killRange (SetN _ n)          = SetN noRange n
  killRange (Rec _ ne)          = killRange1 (Rec noRange) ne
  killRange (RecUpdate _ e ne)  = killRange2 (RecUpdate noRange) e ne
  killRange (Let _ d e)         = killRange2 (Let noRange) d e
  killRange (Paren _ e)         = killRange1 (Paren noRange) e
  killRange (Absurd _)          = Absurd noRange
  killRange (As _ n e)          = killRange2 (As noRange) n e
  killRange (Dot _ e)           = killRange1 (Dot noRange) e
  killRange (ETel t)            = killRange1 ETel t
  killRange (QuoteGoal _ n e)   = killRange2 (QuoteGoal noRange) n e
  killRange (Quote _)           = Quote noRange
  killRange (QuoteTerm _)       = QuoteTerm noRange
  killRange (Unquote _)         = Unquote noRange
  killRange (DontCare e)        = killRange1 DontCare e

instance KillRange ImportDirective where
  killRange (ImportDirective _ u r p) =
    killRange2 (\u r -> ImportDirective noRange u r p) u r

instance KillRange ImportedName where
  killRange (ImportedModule n) = killRange1 ImportedModule n
  killRange (ImportedName   n) = killRange1 ImportedName   n

instance KillRange LamBinding where
  killRange (DomainFree h r b) = killRange2 (\h -> DomainFree h r) h b
  killRange (DomainFull t)     = killRange1 DomainFull t

instance KillRange LHS where
  killRange (LHS p ps r w)     = killRange4 LHS p ps r w
  killRange (Ellipsis _ p r w) = killRange3 (Ellipsis noRange) p r w

instance KillRange ModuleApplication where
  killRange (SectionApp _ t e)    = killRange2 (SectionApp noRange) t e
  killRange (RecordModuleIFS _ q) = killRange1 (RecordModuleIFS noRange) q

instance KillRange e => KillRange (OpApp e) where
  killRange (SyntaxBindingLambda _ l e) = killRange2 (SyntaxBindingLambda noRange) l e
  killRange (Ordinary e)                = killRange1 Ordinary e

instance KillRange Pattern where
  killRange (IdentP q)      = killRange1 IdentP q
  killRange (AppP p n)      = killRange2 AppP p n
  killRange (RawAppP _ p)   = killRange1 (RawAppP noRange) p
  killRange (OpAppP _ n p)  = killRange2 (OpAppP noRange) n p
  killRange (HiddenP _ n)   = killRange1 (HiddenP noRange) n
  killRange (InstanceP _ n) = killRange1 (InstanceP noRange) n
  killRange (ParenP _ p)    = killRange1 (ParenP noRange) p
  killRange (WildP _)       = WildP noRange
  killRange (AbsurdP _)     = AbsurdP noRange
  killRange (AsP _ n p)     = killRange2 (AsP noRange) n p
  killRange (DotP _ e)      = killRange1 (DotP noRange) e
  killRange (LitP l)        = killRange1 LitP l

instance KillRange Pragma where
  killRange (OptionsPragma _ s)           = OptionsPragma noRange s
  killRange (BuiltinPragma _ s e)         = killRange1 (BuiltinPragma noRange s) e
  killRange (CompiledDataPragma _ q s ss) = killRange1 (\q -> CompiledDataPragma noRange q s ss) q
  killRange (CompiledTypePragma _ q s)    = killRange1 (\q -> CompiledTypePragma noRange q s) q
  killRange (CompiledPragma _ q s)        = killRange1 (\q -> CompiledPragma noRange q s) q
  killRange (CompiledEpicPragma _ q s)    = killRange1 (\q -> CompiledEpicPragma noRange q s) q
  killRange (CompiledJSPragma _ q s)      = killRange1 (\q -> CompiledJSPragma noRange q s) q
  killRange (StaticPragma _ q)            = killRange1 (StaticPragma noRange) q
  killRange (ImportPragma _ s)            = ImportPragma noRange s
  killRange (ImpossiblePragma _)          = ImpossiblePragma noRange
  killRange (EtaPragma _ q)               = killRange1 (EtaPragma noRange) q
  killRange (NoTerminationCheckPragma _)  = NoTerminationCheckPragma noRange

instance KillRange Renaming where
  killRange (Renaming i n _) = killRange2 (\i n -> Renaming i n noRange) i n

instance KillRange RHS where
  killRange AbsurdRHS = AbsurdRHS
  killRange (RHS e)   = killRange1 RHS e

instance KillRange TypedBinding where
  killRange (TBind _ b e) = killRange2 (TBind noRange) b e
  killRange (TNoBind e)   = killRange1 TNoBind e

instance KillRange TypedBindings where
  killRange (TypedBindings _ t) = killRange1 (TypedBindings noRange) t

instance KillRange UsingOrHiding where
  killRange (Hiding i) = killRange1 Hiding i
  killRange (Using  i) = killRange1 Using  i

instance KillRange WhereClause where
  killRange NoWhere         = NoWhere
  killRange (AnyWhere d)    = killRange1 AnyWhere d
  killRange (SomeWhere n d) = killRange2 SomeWhere n d
