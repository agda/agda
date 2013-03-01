{-# LANGUAGE DeriveDataTypeable, DeriveFunctor, DeriveFoldable,
             DeriveTraversable, CPP, TemplateHaskell,
             MultiParamTypeClasses, FlexibleInstances,
             TypeSynonymInstances #-}
{-| The abstract syntax. This is what you get after desugaring and scope
    analysis of the concrete syntax. The type checker works on abstract syntax,
    producing internal syntax ("Agda.Syntax.Internal").
-}
module Agda.Syntax.Abstract
    ( module Agda.Syntax.Abstract
    , module Agda.Syntax.Abstract.Name
    ) where

import Prelude hiding (foldl, foldr)
import Control.Applicative
import Data.Sequence (Seq, (<|), (><))
import qualified Data.Sequence as Seq
import Data.Foldable as Fold
import Data.Traversable
import Data.Map (Map)
import Data.Typeable (Typeable)

import qualified Agda.Syntax.Concrete as C
import Agda.Syntax.Concrete.Pretty ()
import Agda.Syntax.Info
import Agda.Syntax.Common hiding (Arg, Dom, NamedArg, ArgInfo)
import qualified Agda.Syntax.Common as Common
import Agda.Syntax.Fixity
import Agda.Syntax.Position
import Agda.Syntax.Abstract.Name
import Agda.Syntax.Abstract.Name as A (QNamed)
import Agda.Syntax.Literal
import Agda.Syntax.Scope.Base

import Agda.Utils.Geniplate
import Agda.Utils.Tuple

#include "../undefined.h"
import Agda.Utils.Impossible

type Color      = Expr
type Arg a      = Common.Arg Color a
type Dom a      = Common.Dom Color a
type NamedArg a = Common.NamedArg Color a
type ArgInfo    = Common.ArgInfo Color
type Args       = [NamedArg Expr]

instance Eq Color where
  Var x == Var y = x == y
  Def x == Def y = x == y
  -- TODO guilhem:
  _ == _         = __IMPOSSIBLE__

instance Ord Color where
  Var x <= Var y = x <= y
  Def x <= Def y = x <= y
  -- TODO guilhem:
  _ <= _         = __IMPOSSIBLE__

data Expr
        = Var  Name			     -- ^ Bound variables
        | Def  QName			     -- ^ Constants (i.e. axioms, functions, projections, and datatypes)
        | Con  AmbiguousQName		     -- ^ Constructors
	| Lit Literal			     -- ^ Literals
	| QuestionMark MetaInfo		     -- ^ meta variable for interaction
        | Underscore   MetaInfo		     -- ^ meta variable for hidden argument (must be inferred locally)
        | App  ExprInfo Expr (NamedArg Expr) -- ^
	| WithApp ExprInfo Expr [Expr]	     -- ^ with application
        | Lam  ExprInfo LamBinding Expr	     -- ^
        | AbsurdLam ExprInfo Hiding
        | ExtendedLam ExprInfo DefInfo QName [Clause]
        | Pi   ExprInfo Telescope Expr	     -- ^
	| Fun  ExprInfo (Arg Expr) Expr	     -- ^ independent function space
        | Set  ExprInfo Integer              -- ^ Set, Set1, Set2, ...
        | Prop ExprInfo			     -- ^
        | Let  ExprInfo [LetBinding] Expr    -- ^
        | ETel Telescope                     -- ^ only used when printing telescopes
	| Rec  ExprInfo [(C.Name, Expr)]     -- ^ record construction
	| RecUpdate ExprInfo Expr [(C.Name, Expr)]     -- ^ record update
	| ScopedExpr ScopeInfo Expr	     -- ^ scope annotation
        | QuoteGoal ExprInfo Name Expr       -- ^ binds @Name@ to current type in @Expr@
        | Quote ExprInfo                     -- ^
        | QuoteTerm ExprInfo                 -- ^
        | Unquote ExprInfo                   -- ^ The splicing construct: unquote ...
        | DontCare Expr                      -- ^ for printing DontCare from Syntax.Internal
        | PatternSyn QName
  deriving (Typeable, Show)

data Declaration
	= Axiom      DefInfo ArgInfo QName Expr            -- ^ postulate (can be irrelevant and colored, but not hidden)
	| Field      DefInfo QName (Arg Expr)		   -- ^ record field
	| Primitive  DefInfo QName Expr			   -- ^ primitive function
	| Mutual     MutualInfo [Declaration]              -- ^ a bunch of mutually recursive definitions
	| Section    ModuleInfo ModuleName [TypedBindings] [Declaration]
	| Apply	     ModuleInfo ModuleName ModuleApplication (Map QName QName) (Map ModuleName ModuleName)
	| Import     ModuleInfo ModuleName
	| Pragma     Range	Pragma
        | Open       ModuleInfo ModuleName
          -- ^ only retained for highlighting purposes
        | FunDef     DefInfo QName Delayed [Clause] -- ^ sequence of function clauses
        | DataSig    DefInfo QName Telescope Expr -- ^ lone data signature
            -- ^ the 'LamBinding's are 'DomainFree' and binds the parameters of the datatype.
        | DataDef    DefInfo QName [LamBinding] [Constructor]
            -- ^ the 'LamBinding's are 'DomainFree' and binds the parameters of the datatype.
        | RecSig     DefInfo QName Telescope Expr -- ^ lone record signature
        | RecDef     DefInfo QName (Maybe Induction) (Maybe QName) [LamBinding] Expr [Declaration]
            -- ^ The 'Expr' gives the constructor type telescope, @(x1 : A1)..(xn : An) -> Prop@,
            --   and the optional name is the constructor's name.
	| ScopedDecl ScopeInfo [Declaration]  -- ^ scope annotation
        deriving (Typeable, Show)

class GetDefInfo a where
  getDefInfo :: a -> Maybe DefInfo

instance GetDefInfo Declaration where
  getDefInfo (Axiom i _ _ _) = Just i
  getDefInfo (Field i _ _) = Just i
  getDefInfo (Primitive i _ _) = Just i
  getDefInfo (ScopedDecl _ (d:_)) = getDefInfo d
  getDefInfo (FunDef i _ _ _) = Just i
  getDefInfo (DataSig i _ _ _) = Just i
  getDefInfo (DataDef i _ _ _) = Just i
  getDefInfo (RecSig i _ _ _) = Just i
  getDefInfo (RecDef i _ _ _ _ _ _) = Just i
  getDefInfo _ = Nothing

data ModuleApplication = SectionApp [TypedBindings] ModuleName [NamedArg Expr]
                       | RecordModuleIFS ModuleName
  deriving (Typeable, Show)

data Pragma = OptionsPragma [String]
	    | BuiltinPragma String Expr
            | CompiledPragma QName String
            | CompiledTypePragma QName String
            | CompiledDataPragma QName String [String]
            | CompiledEpicPragma QName String
            | CompiledJSPragma QName String
            | StaticPragma QName
            | EtaPragma QName
  deriving (Typeable, Show)

data LetBinding = LetBind LetInfo ArgInfo Name Expr Expr -- ^ LetBind info rel name type defn
                | LetPatBind LetInfo Pattern Expr -- ^ irrefutable pattern binding
                | LetApply ModuleInfo ModuleName ModuleApplication (Map QName QName) (Map ModuleName ModuleName)
                | LetOpen ModuleInfo ModuleName     -- ^ only for highlighting and abstractToConcrete
  deriving (Typeable, Show)

-- | Only 'Axiom's.
type TypeSignature  = Declaration
type Constructor    = TypeSignature
type Field          = TypeSignature

-- | A lambda binding is either domain free or typed.
data LamBinding
	= DomainFree ArgInfo Name   -- ^ . @x@ or @{x}@ or @.x@ or @.{x}@
	| DomainFull TypedBindings  -- ^ . @(xs:e)@ or @{xs:e}@
  deriving (Typeable, Show)

-- | Typed bindings with hiding information.
data TypedBindings = TypedBindings Range (Arg TypedBinding)
	    -- ^ . @(xs : e)@ or @{xs : e}@
  deriving (Typeable, Show)

-- | A typed binding. Appears in dependent function spaces, typed lambdas, and
--   telescopes. I might be tempting to simplify this to only bind a single
--   name at a time. This would mean that we would have to typecheck the type
--   several times (@x,y:A@ vs. @x:A; y:A@). In most cases this wouldn't
--   really be a problem, but it's good principle to not do extra work unless
--   you have to.
data TypedBinding = TBind Range [Name] Expr
		  | TNoBind Expr
  deriving (Typeable, Show)

type Telescope	= [TypedBindings]

-- | We could throw away @where@ clauses at this point and translate them to
--   @let@. It's not obvious how to remember that the @let@ was really a
--   @where@ clause though, so for the time being we keep it here.
data Clause	= Clause
  { clauseLHS        :: LHS
  , clauseRHS        :: RHS
  , clauseWhereDecls :: [Declaration]
  } deriving (Typeable, Show)

data RHS	= RHS Expr
		| AbsurdRHS
		| WithRHS QName [Expr] [Clause] -- ^ The 'QName' is the name of the with function.
                | RewriteRHS [QName] [Expr] RHS [Declaration]
                    -- ^ The 'QName's are the names of the generated with functions.
                    --   One for each 'Expr'.
                    --   The RHS shouldn't be another RewriteRHS
  deriving (Typeable, Show)

-- | The lhs of a clause in spine view (inside-out).
--   Projection patterns are contained in @spLhsPats@,
--   represented as @DefP d []@.
data SpineLHS = SpineLHS
  { spLhsInfo     :: LHSInfo             -- ^ Range.
  , spLhsDefName  :: QName               -- ^ Name of function we are defining.
  , spLhsPats     :: [NamedArg Pattern]  -- ^ Function parameters (patterns).
  , spLhsWithPats :: [Pattern]           -- ^ @with@ patterns (after @|@).
  }
  deriving (Typeable, Show)

-- | The lhs of a clause in projection-application view (outside-in).
--   Projection patters are represented as 'LHSProj's.
data LHS = LHS
  { lhsInfo     :: LHSInfo               -- ^ Range.
  , lhsCore     :: LHSCore               -- ^ Copatterns.
  , lhsWithPats :: [Pattern]             -- ^ @with@ patterns (after @|@).
  }
  deriving (Typeable, Show)

-- | The lhs minus @with@-patterns in projection-application view.
--   Parameterised over the type @e@ of dot patterns.
data LHSCore' e
    -- | The head applied to ordinary patterns.
  = LHSHead  { lhsDefName  :: QName                    -- ^ Head @f@.
             , lhsPats     :: [NamedArg (Pattern' e)]  -- ^ Applied to patterns @ps@.
             }
    -- | Projection
  | LHSProj  { lhsDestructor :: QName
               -- ^ Record projection identifier.
             , lhsPatsLeft   :: [NamedArg (Pattern' e)]
               -- ^ Indices of the projection.
               --   Currently none @[]@, since we do not have indexed records.
             , lhsFocus      :: NamedArg (LHSCore' e)
               -- ^ Main branch.
             , lhsPatsRight  :: [NamedArg (Pattern' e)]
               -- ^ Further applied to patterns.
             }
  deriving (Typeable, Show, Functor, Foldable, Traversable)

type LHSCore = LHSCore' Expr

lhsToSpine :: LHS -> SpineLHS
lhsToSpine (LHS i core wps) = SpineLHS i f ps wps
  where QNamed f ps = lhsCoreToSpine core

lhsCoreToSpine :: LHSCore' e -> A.QNamed [NamedArg (Pattern' e)]
lhsCoreToSpine (LHSHead f ps) = QNamed f ps
lhsCoreToSpine (LHSProj d ps1 h ps2) = (++ (p : ps2)) <$> lhsCoreToSpine (namedArg h)
  where p = updateNamedArg (const $ DefP i d ps1) h
        i = PatRange noRange

-- spineToLhsCore ::

-- | Used for checking pattern linearity.
lhsCoreAllPatterns :: LHSCore' e -> [Pattern' e]
lhsCoreAllPatterns = map namedArg . qnamed . lhsCoreToSpine
{- OLD code, dumps projection patterns, superfluous
lhsCoreAllPatterns (LHSHead f ps) = map namedArg ps
lhsCoreAllPatterns (LHSProj d ps1 l ps2) =
  map namedArg ps1 ++
  lhsCoreAllPatterns (namedArg l) ++
  map namedArg ps2
-}

-- | Used in AbstractToConcrete.
lhsCoreToPattern :: LHSCore -> Pattern
lhsCoreToPattern lc =
  case lc of
    LHSHead f aps -> DefP noInfo f aps
    LHSProj d aps1 lhscore aps2 -> DefP noInfo d $
      aps1 ++ fmap (fmap lhsCoreToPattern) lhscore : aps2
  where noInfo = PatRange noRange -- TODO, preserve range!

mapLHSHead :: (QName -> [NamedArg Pattern] -> LHSCore) -> LHSCore -> LHSCore
mapLHSHead f (LHSHead x ps)        = f x ps
mapLHSHead f (LHSProj d ps1 l ps2) =
  LHSProj d ps1 (fmap (fmap (mapLHSHead f)) l) ps2

{- UNUSED
mapLHSHeadM :: (Monad m) => (QName -> [NamedArg Pattern] -> m LHSCore) -> LHSCore -> m LHSCore
mapLHSHeadM f (LHSHead x ps)        = f x ps
mapLHSHeadM f (LHSProj d ps1 l ps2) = do
  l <- mapLHSHead f l
  return $ LHSProj d ps1 l ps2
-}

-- | Parameterised over the type of dot patterns.
data Pattern' e
  = VarP Name
  | ConP PatInfo AmbiguousQName [NamedArg (Pattern' e)]
  | DefP PatInfo QName          [NamedArg (Pattern' e)]
    -- ^ Defined pattern: function definition @f ps@ or destructor pattern @d p ps@.
  | WildP PatInfo
  | AsP PatInfo Name (Pattern' e)
  | DotP PatInfo e
  | AbsurdP PatInfo
  | LitP Literal
  | ImplicitP PatInfo
    -- ^ Generated at type checking for implicit arguments.
  | PatternSynP PatInfo QName [NamedArg (Pattern' e)]
  deriving (Typeable, Show, Functor, Foldable, Traversable)

type Pattern  = Pattern' Expr
type Patterns = [NamedArg Pattern]

{--------------------------------------------------------------------------
    Instances
 --------------------------------------------------------------------------}

instance HasRange LamBinding where
    getRange (DomainFree _ x) = getRange x
    getRange (DomainFull b)   = getRange b

instance HasRange TypedBindings where
    getRange (TypedBindings r _) = r

instance HasRange TypedBinding where
    getRange (TBind r _ _) = r
    getRange (TNoBind e)   = getRange e

instance HasRange Expr where
    getRange (Var x)		   = getRange x
    getRange (Def x)		   = getRange x
    getRange (Con x)		   = getRange x
    getRange (Lit l)		   = getRange l
    getRange (QuestionMark i)	   = getRange i
    getRange (Underscore  i)	   = getRange i
    getRange (App i _ _)	   = getRange i
    getRange (WithApp i _ _)	   = getRange i
    getRange (Lam i _ _)	   = getRange i
    getRange (AbsurdLam i _)       = getRange i
    getRange (ExtendedLam i _ _ _) = getRange i
    getRange (Pi i _ _)		   = getRange i
    getRange (Fun i _ _)	   = getRange i
    getRange (Set i _)		   = getRange i
    getRange (Prop i)		   = getRange i
    getRange (Let i _ _)	   = getRange i
    getRange (Rec i _)		   = getRange i
    getRange (RecUpdate i _ _)     = getRange i
    getRange (ETel tel)            = getRange tel
    getRange (ScopedExpr _ e)	   = getRange e
    getRange (QuoteGoal _ _ e)	   = getRange e
    getRange (Quote i)  	   = getRange i
    getRange (QuoteTerm i)  	   = getRange i
    getRange (Unquote i)  	   = getRange i
    getRange (DontCare{})          = noRange
    getRange (PatternSyn x)        = getRange x

instance HasRange Declaration where
    getRange (Axiom      i _ _ _    ) = getRange i
    getRange (Field      i _ _      ) = getRange i
    getRange (Mutual     i _        ) = getRange i
    getRange (Section    i _ _ _    ) = getRange i
    getRange (Apply	 i _ _ _ _  ) = getRange i
    getRange (Import     i _	    ) = getRange i
    getRange (Primitive  i _ _	    ) = getRange i
    getRange (Pragma	 i _	    ) = getRange i
    getRange (Open       i _        ) = getRange i
    getRange (ScopedDecl _ d	    ) = getRange d
    getRange (FunDef     i _ _ _    ) = getRange i
    getRange (DataSig    i _ _ _    ) = getRange i
    getRange (DataDef    i _ _ _    ) = getRange i
    getRange (RecSig     i _ _ _    ) = getRange i
    getRange (RecDef   i _ _ _ _ _ _) = getRange i

instance HasRange (Pattern' e) where
    getRange (VarP x)	         = getRange x
    getRange (ConP i _ _)        = getRange i
    getRange (DefP i _ _)        = getRange i
    getRange (WildP i)	         = getRange i
    getRange (ImplicitP i)       = getRange i
    getRange (AsP i _ _)         = getRange i
    getRange (DotP i _)          = getRange i
    getRange (AbsurdP i)         = getRange i
    getRange (LitP l)	         = getRange l
    getRange (PatternSynP i _ _) = getRange i

instance HasRange LHS where
    getRange (LHS i _ _)   = getRange i

instance HasRange (LHSCore' e) where
    getRange (LHSHead f ps) = fuseRange f ps
    getRange (LHSProj d ps1 lhscore ps2) = d `fuseRange` ps1 `fuseRange` lhscore `fuseRange` ps2

instance HasRange Clause where
    getRange (Clause lhs rhs ds) = getRange (lhs,rhs,ds)

instance HasRange RHS where
    getRange AbsurdRHS                = noRange
    getRange (RHS e)                  = getRange e
    getRange (WithRHS _ e cs)         = fuseRange e cs
    getRange (RewriteRHS _ es rhs wh) = getRange (es, rhs, wh)

instance HasRange LetBinding where
    getRange (LetBind  i _ _ _ _     ) = getRange i
    getRange (LetPatBind  i _ _      ) = getRange i
    getRange (LetApply i _ _ _ _     ) = getRange i
    getRange (LetOpen  i _           ) = getRange i

-- setRange for patterns applies the range to the outermost pattern constructor
instance SetRange (Pattern' a) where
    setRange r (VarP x)             = VarP (setRange r x)
    setRange r (ConP _ ns as)       = ConP (PatRange r) (AmbQ $ map (setRange r) $ unAmbQ ns) as
    setRange r (DefP _ n as)        = DefP (PatRange r) (setRange r n) as
    setRange r (WildP _)            = WildP (PatRange r)
    setRange r (ImplicitP _)        = ImplicitP (PatRange r)
    setRange r (AsP _ n p)          = AsP (PatRange r) (setRange r n) p
    setRange r (DotP _ e)           = DotP (PatRange r) e
    setRange r (AbsurdP _)          = AbsurdP (PatRange r)
    setRange r (LitP l)             = LitP (setRange r l)
    setRange r (PatternSynP _ n as) = PatternSynP (PatRange r) (setRange r n) as

instance KillRange LamBinding where
  killRange (DomainFree info x) = killRange1 (DomainFree info) x
  killRange (DomainFull b)      = killRange1 DomainFull b

instance KillRange TypedBindings where
  killRange (TypedBindings r b) = TypedBindings (killRange r) (killRange b)

instance KillRange TypedBinding where
  killRange (TBind r xs e) = killRange3 TBind r xs e
  killRange (TNoBind e)    = killRange1 TNoBind e

instance KillRange Expr where
  killRange (Var x)                = killRange1 Var x
  killRange (Def x)                = killRange1 Def x
  killRange (Con x)                = killRange1 Con x
  killRange (Lit l)                = killRange1 Lit l
  killRange (QuestionMark i)       = killRange1 QuestionMark i
  killRange (Underscore  i)        = killRange1 Underscore i
  killRange (App i e1 e2)          = killRange3 App i e1 e2
  killRange (WithApp i e es)       = killRange3 WithApp i e es
  killRange (Lam i b e)            = killRange3 Lam i b e
  killRange (AbsurdLam i h)        = killRange1 AbsurdLam i h
  killRange (ExtendedLam i n d ps) = killRange4 ExtendedLam i n d ps
  killRange (Pi i a b)             = killRange3 Pi i a b
  killRange (Fun i a b)            = killRange3 Fun i a b
  killRange (Set i n)              = Set (killRange i) n
  killRange (Prop i)               = killRange1 Prop i
  killRange (Let i ds e)           = killRange3 Let i ds e
  killRange (Rec i fs)             = Rec (killRange i) (map (id -*- killRange) fs)
  killRange (RecUpdate i e fs)     = RecUpdate (killRange i)
                                               (killRange e)
                                               (map (id -*- killRange) fs)
  killRange (ETel tel)             = killRange1 ETel tel
  killRange (ScopedExpr s e)       = killRange1 (ScopedExpr s) e
  killRange (QuoteGoal i x e)      = killRange3 QuoteGoal i x e
  killRange (Quote i)              = killRange1 Quote i
  killRange (QuoteTerm i)          = killRange1 QuoteTerm i
  killRange (Unquote i)            = killRange1 Unquote i
  killRange (DontCare e)           = DontCare e
  killRange (PatternSyn x)         = killRange1 PatternSyn x

instance KillRange Declaration where
  killRange (Axiom      i rel a b     ) = killRange4 Axiom      i rel a b
  killRange (Field      i a b         ) = killRange3 Field      i a b
  killRange (Mutual     i a           ) = killRange2 Mutual     i a
  killRange (Section    i a b c       ) = killRange4 Section    i a b c
  killRange (Apply      i a b c d     ) = killRange3 Apply      i a b c d
   -- the last two arguments of Apply are name maps, so nothing to kill
  killRange (Import     i a           ) = killRange2 Import     i a
  killRange (Primitive  i a b         ) = killRange3 Primitive  i a b
  killRange (Pragma     i a           ) = Pragma (killRange i) a
  killRange (Open       i x           ) = killRange2 Open       i x
  killRange (ScopedDecl a d           ) = killRange1 (ScopedDecl a) d
  killRange (FunDef  i a b c          ) = killRange4 FunDef  i a b c
  killRange (DataSig i a b c          ) = killRange4 DataSig i a b c
  killRange (DataDef i a b c          ) = killRange4 DataDef i a b c
  killRange (RecSig  i a b c          ) = killRange4 RecSig  i a b c
  killRange (RecDef  i a b c d e f    ) = killRange7 RecDef  i a b c d e f

instance KillRange ModuleApplication where
  killRange (SectionApp a b c  ) = killRange3 SectionApp a b c
  killRange (RecordModuleIFS a ) = killRange1 RecordModuleIFS a

instance KillRange x => KillRange (ThingWithFixity x) where
  killRange (ThingWithFixity c f) = ThingWithFixity (killRange c) f

instance KillRange e => KillRange (Pattern' e) where
  killRange (VarP x)            = killRange1 VarP x
  killRange (ConP i a b)        = killRange3 ConP i a b
  killRange (DefP i a b)        = killRange3 DefP i a b
  killRange (WildP i)           = killRange1 WildP i
  killRange (ImplicitP i)       = killRange1 ImplicitP i
  killRange (AsP i a b)         = killRange3 AsP i a b
  killRange (DotP i a)          = killRange2 DotP i a
  killRange (AbsurdP i)         = killRange1 AbsurdP i
  killRange (LitP l)            = killRange1 LitP l
  killRange (PatternSynP i a p) = killRange3 PatternSynP i a p

instance KillRange LHS where
  killRange (LHS i a b)   = killRange3 LHS i a b

instance KillRange e => KillRange (LHSCore' e) where
  killRange (LHSHead a b)     = killRange2 LHSHead a b
  killRange (LHSProj a b c d) = killRange4 LHSProj a b c d

instance KillRange Clause where
  killRange (Clause lhs rhs ds) = killRange3 Clause lhs rhs ds

instance KillRange RHS where
  killRange AbsurdRHS                = AbsurdRHS
  killRange (RHS e)                  = killRange1 RHS e
  killRange (WithRHS q e cs)         = killRange3 WithRHS q e cs
  killRange (RewriteRHS x es rhs wh) = killRange4 RewriteRHS x es rhs wh

instance KillRange LetBinding where
  killRange (LetBind    i info a b c) = killRange5 LetBind  i info a b c
  killRange (LetPatBind i a b       ) = killRange3 LetPatBind i a b
  killRange (LetApply   i a b c d   ) = killRange3 LetApply i a b c d
  killRange (LetOpen    i x         ) = killRange2 LetOpen  i x

instanceUniverseBiT' [] [t| (Declaration, QName)          |]
instanceUniverseBiT' [] [t| (Declaration, AmbiguousQName) |]
instanceUniverseBiT' [] [t| (Declaration, Expr)           |]
instanceUniverseBiT' [] [t| (Declaration, LetBinding)     |]
instanceUniverseBiT' [] [t| (Declaration, LamBinding)     |]
instanceUniverseBiT' [] [t| (Declaration, TypedBinding)   |]
instanceUniverseBiT' [] [t| (Declaration, Pattern)        |]
instanceUniverseBiT' [] [t| (Declaration, Declaration)    |]
instanceUniverseBiT' [] [t| (Declaration, ModuleName)     |]
instanceUniverseBiT' [] [t| (Declaration, ModuleInfo)     |]

------------------------------------------------------------------------
-- Queries
------------------------------------------------------------------------

-- | Extracts all the names which are declared in a 'Declaration'.
-- This does not include open public or let expressions, but it does
-- include local modules, where clauses and the names of extended
-- lambdas.

allNames :: Declaration -> Seq QName
allNames (Axiom     _ _ q _)      = Seq.singleton q
allNames (Field     _   q _)      = Seq.singleton q
allNames (Primitive _   q _)      = Seq.singleton q
allNames (Mutual     _ defs)      = Fold.foldMap allNames defs
allNames (DataSig _ q _ _)        = Seq.singleton q
allNames (DataDef _ q _ decls)    = q <| Fold.foldMap allNames decls
allNames (RecSig _ q _ _)         = Seq.singleton q
allNames (RecDef _ q _ c _ _ decls) =
  q <| foldMap Seq.singleton c >< Fold.foldMap allNames decls
allNames (FunDef _ q _ cls)       = q <| Fold.foldMap allNamesC cls
  where
  allNamesC :: Clause -> Seq QName
  allNamesC (Clause _ rhs decls) = allNamesR rhs ><
                                   Fold.foldMap allNames decls

  allNamesR :: RHS -> Seq QName
  allNamesR (RHS e)               = allNamesE e
  allNamesR AbsurdRHS {}          = Seq.empty
  allNamesR (WithRHS q _ cls)     = q <| Fold.foldMap allNamesC cls
  allNamesR (RewriteRHS qs _ rhs cls) =
    Seq.fromList qs >< allNamesR rhs
                    >< Fold.foldMap allNames cls

  allNamesE :: Expr -> Seq QName
  allNamesE Var {}                       = Seq.empty
  allNamesE Def {}                       = Seq.empty
  allNamesE Con {}                       = Seq.empty
  allNamesE Lit {}                       = Seq.empty
  allNamesE QuestionMark {}              = Seq.empty
  allNamesE Underscore {}                = Seq.empty
  allNamesE (App _ e1 e2)                = Fold.foldMap allNamesE [e1, namedThing (unArg e2)]
  allNamesE (WithApp _ e es)             = Fold.foldMap allNamesE (e : es)
  allNamesE (Lam _ b e)                  = allNamesLam b >< allNamesE e
  allNamesE AbsurdLam {}                 = Seq.empty
  allNamesE (ExtendedLam _ _ q cls)      = q <| Fold.foldMap allNamesC cls
  allNamesE (Pi _ tel e)                 = Fold.foldMap allNamesBinds tel ><
                                                        allNamesE e
  allNamesE (Fun _ (Common.Arg _ e1) e2) = Fold.foldMap allNamesE [e1, e2]
  allNamesE Set {}                       = Seq.empty
  allNamesE Prop {}                      = Seq.empty
  allNamesE (Let _ lbs e)                = Fold.foldMap allNamesLet lbs ><
                                                        allNamesE e
  allNamesE ETel {}                      = __IMPOSSIBLE__
  allNamesE (Rec _ fields)               = Fold.foldMap allNamesE (map snd fields)
  allNamesE (RecUpdate _ e fs)           = allNamesE e >< Fold.foldMap allNamesE (map snd fs)
  allNamesE (ScopedExpr _ e)             = allNamesE e
  allNamesE (QuoteGoal _ _ e)            = allNamesE e
  allNamesE Quote {}                     = Seq.empty
  allNamesE QuoteTerm {}                 = Seq.empty
  allNamesE Unquote {}                   = Seq.empty
  allNamesE DontCare {}                  = Seq.empty
  allNamesE (PatternSyn x)               = Seq.empty

  allNamesLam :: LamBinding -> Seq QName
  allNamesLam DomainFree {}      = Seq.empty
  allNamesLam (DomainFull binds) = allNamesBinds binds

  allNamesBinds :: TypedBindings -> Seq QName
  allNamesBinds (TypedBindings _ (Common.Arg _ (TBind _ _ e))) = allNamesE e
  allNamesBinds (TypedBindings _ (Common.Arg _ (TNoBind e)))   = allNamesE e

  allNamesLet :: LetBinding -> Seq QName
  allNamesLet (LetBind _ _ _ e1 e2)  = Fold.foldMap allNamesE [e1, e2]
  allNamesLet (LetPatBind _ _ e)     = allNamesE e
  allNamesLet (LetApply _ _ app _ _) = allNamesApp app
  allNamesLet LetOpen {}             = Seq.empty

  allNamesApp :: ModuleApplication -> Seq QName
  allNamesApp (SectionApp bindss _ es) = Fold.foldMap allNamesBinds bindss ><
                                         Fold.foldMap allNamesE (map namedArg es)
  allNamesApp RecordModuleIFS {}       = Seq.empty

allNames (Section _ _ _ decls) = Fold.foldMap allNames decls
allNames Apply {}              = Seq.empty
allNames Import {}             = Seq.empty
allNames Pragma {}             = Seq.empty
allNames Open {}               = Seq.empty
allNames (ScopedDecl _ decls)  = Fold.foldMap allNames decls

-- | The name defined by the given axiom.
--
-- Precondition: The declaration has to be an 'Axiom'.

axiomName :: Declaration -> QName
axiomName (Axiom _ _ q _) = q
axiomName _             = __IMPOSSIBLE__

-- | Are we in an abstract block?
--
--   In that case some definition is abstract.
class AnyAbstract a where
  anyAbstract :: a -> Bool

instance AnyAbstract a => AnyAbstract [a] where
  anyAbstract = Fold.any anyAbstract

instance AnyAbstract Declaration where
  anyAbstract (Axiom i _ _ _)        = defAbstract i == AbstractDef
  anyAbstract (Field i _ _)          = defAbstract i == AbstractDef
  anyAbstract (Mutual     _ ds)      = anyAbstract ds
  anyAbstract (ScopedDecl _ ds)      = anyAbstract ds
  anyAbstract (Section _ _ _ ds)     = anyAbstract ds
  anyAbstract (FunDef i _ _ _)       = defAbstract i == AbstractDef
  anyAbstract (DataDef i _ _ _)      = defAbstract i == AbstractDef
  anyAbstract (RecDef i _ _ _ _ _ _) = defAbstract i == AbstractDef
  anyAbstract (DataSig i _ _ _)      = defAbstract i == AbstractDef
  anyAbstract (RecSig i _ _ _)       = defAbstract i == AbstractDef
  anyAbstract _                      = __IMPOSSIBLE__

app   = foldl (App (ExprRange noRange))

patternToExpr :: Pattern -> Expr
patternToExpr (VarP x)            = Var x
patternToExpr (ConP _ c ps)       =
          Con c `app` map (fmap (fmap patternToExpr)) ps
patternToExpr (DefP _ f ps)       =
          Def f `app` map (fmap (fmap patternToExpr)) ps
patternToExpr (WildP _)           = Underscore emptyMetaInfo
patternToExpr (AsP _ _ p)         = patternToExpr p
patternToExpr (DotP _ e)          = e
patternToExpr (AbsurdP _)         = Underscore emptyMetaInfo  -- TODO: could this happen?
patternToExpr (LitP l)            = Lit l
patternToExpr (ImplicitP _)       = Underscore emptyMetaInfo
patternToExpr (PatternSynP _ _ _) = __IMPOSSIBLE__

type PatternSynDefn = ([Name], Pattern)
type PatternSynDefns = Map QName PatternSynDefn

lambdaLiftExpr :: [Name] -> Expr -> Expr
lambdaLiftExpr []     e = e
lambdaLiftExpr (n:ns) e = Lam (ExprRange noRange)
                                     (DomainFree defaultArgInfo n) $
                                     lambdaLiftExpr ns e

substPattern :: [(Name, Pattern)] -> Pattern -> Pattern
substPattern s p = case p of
  VarP z      -> case lookup z s of
    Nothing -> p
    Just x  -> x
  ConP i q ps -> ConP i q (fmap (fmap (fmap (substPattern s))) ps)
  WildP i     -> p
  DotP i e    -> DotP i (substExpr (map (fmap patternToExpr) s) e)
  AbsurdP i   -> p
  LitP l      -> p
  _           -> __IMPOSSIBLE__ -- Implicits (generated at TC time),
                                -- pattern synonyms (already gone), and
                                -- @-patterns (not supported anyways).

substExpr :: [(Name, Expr)] -> Expr -> Expr
substExpr s e = case e of
  Var n -> case lookup n s of
    Nothing -> e
    Just z  -> z
  Def _                 -> e
  Con _	                -> e
  Lit _                 -> e
  QuestionMark _        -> e
  Underscore   _        -> e
  App  i e e'           -> App i (substExpr s e)
                                 (fmap (fmap (substExpr s)) e')
  WithApp i e es        -> WithApp i (substExpr s e)
                                     (fmap (substExpr s) es)
  Lam  i lb e           -> Lam i lb (substExpr s e)
  AbsurdLam i h         -> e
  ExtendedLam i di n cs -> __IMPOSSIBLE__   -- Maybe later...
  Pi   i t e            -> Pi i (fmap (substTypedBindings s) t)
                                (substExpr s e)
  Fun  i ae e           -> Fun i (fmap (substExpr s) ae)
                                 (substExpr s e)
  Set  i n              -> e
  Prop i                -> e
  Let  i ls e           -> Let i (fmap (substLetBinding s) ls)
                                 (substExpr s e)
  ETel t                -> e
  Rec  i nes            -> Rec i (fmap (fmap (substExpr s)) nes)
  RecUpdate i e nes     -> RecUpdate i (substExpr s e)
                                       (fmap (fmap (substExpr s)) nes)
  -- XXX: Do we need to do more with ScopedExprs?
  ScopedExpr si e       -> ScopedExpr si (substExpr s e)
  QuoteGoal i n e       -> QuoteGoal i n (substExpr s e)
  Quote i               -> e
  QuoteTerm i           -> e
  Unquote i             -> e
  DontCare e            -> DontCare (substExpr s e)
  PatternSyn x          -> e

substLetBinding :: [(Name, Expr)] -> LetBinding -> LetBinding
substLetBinding s lb = case lb of
  LetBind i r n e e' -> LetBind i r n (substExpr s e) (substExpr s e')
  LetPatBind i p e   -> LetPatBind i p (substExpr s e) -- Andreas, 2012-06-04: what about the pattern p
  _                  -> lb

substTypedBindings :: [(Name, Expr)] -> TypedBindings -> TypedBindings
substTypedBindings s (TypedBindings r atb) = TypedBindings r
    (fmap (substTypedBinding s) atb)

substTypedBinding :: [(Name, Expr)] -> TypedBinding -> TypedBinding
substTypedBinding s tb = case tb of
  TBind r ns e -> TBind r ns $ substExpr s e
  TNoBind e    -> TNoBind $ substExpr s e
