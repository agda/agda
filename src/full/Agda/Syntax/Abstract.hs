{-# LANGUAGE DeriveDataTypeable, CPP #-}
{-| The abstract syntax. This is what you get after desugaring and scope
    analysis of the concrete syntax. The type checker works on abstract syntax,
    producing internal syntax ("Agda.Syntax.Internal").
-}
module Agda.Syntax.Abstract
    ( module Agda.Syntax.Abstract
    , module Agda.Syntax.Abstract.Name
    ) where

import Prelude hiding (foldr)
import Control.Applicative
import Data.Sequence (Seq, (<|), (><))
import qualified Data.Sequence as Seq
import Data.Foldable as Fold
import Data.Traversable
import Data.Map (Map)
import Data.Generics (Typeable, Data)

import qualified Agda.Syntax.Concrete as C
import Agda.Syntax.Concrete.Pretty ()
import Agda.Syntax.Info
import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Abstract.Name
import Agda.Syntax.Literal
import Agda.Syntax.Scope.Base

import Agda.Utils.Tuple

#include "../undefined.h"
import Agda.Utils.Impossible

data Expr
        = Var  Name			     -- ^ Bound variables
        | Def  QName			     -- ^ Constants (i.e. axioms, functions, and datatypes)
        | Con  AmbiguousQName		     -- ^ Constructors
	| Lit Literal			     -- ^ Literals
	| QuestionMark MetaInfo		     -- ^ meta variable for interaction
        | Underscore   MetaInfo		     -- ^ meta variable for hidden argument (must be inferred locally)
        | App  ExprInfo Expr (NamedArg Expr) -- ^
	| WithApp ExprInfo Expr [Expr]	     -- ^ with application
        | Lam  ExprInfo LamBinding Expr	     -- ^
        | AbsurdLam ExprInfo Hiding
        | Pi   ExprInfo Telescope Expr	     -- ^
	| Fun  ExprInfo (Arg Expr) Expr	     -- ^ independent function space
        | Set  ExprInfo Nat		     -- ^
        | Prop ExprInfo			     -- ^
        | Let  ExprInfo [LetBinding] Expr    -- ^
        | ETel Telescope                     -- ^ only used when printing telescopes
	| Rec  ExprInfo [(C.Name, Expr)]     -- ^ record construction
	| ScopedExpr ScopeInfo Expr	     -- ^ scope annotation
        | QuoteGoal ExprInfo Name Expr       -- ^
        | Quote ExprInfo                     -- ^
        | DontCare                           -- ^ for printing DontCare from Syntax.Internal
  deriving (Typeable, Data, Show)

data Declaration
	= Axiom      DefInfo Relevance QName Expr          -- ^ postulate
	| Field      DefInfo QName (Arg Expr)		   -- ^ record field
	| Primitive  DefInfo QName Expr			   -- ^ primitive function
	| Definition DeclInfo [TypeSignature] [Definition] -- ^ a bunch of mutually recursive definitions
	| Section    ModuleInfo ModuleName [TypedBindings] [Declaration]
	| Apply	     ModuleInfo ModuleName [TypedBindings] ModuleName [NamedArg Expr] (Map QName QName) (Map ModuleName ModuleName)
	| Import     ModuleInfo ModuleName
	| Pragma     Range	Pragma
        | Open       ModuleInfo ModuleName
          -- ^ only retained for highlighting purposes
	| ScopedDecl ScopeInfo [Declaration]  -- ^ scope annotation
  deriving (Typeable, Data, Show)

data Pragma = OptionsPragma [String]
	    | BuiltinPragma String Expr
            | CompiledPragma QName String
            | CompiledTypePragma QName String
            | CompiledDataPragma QName String [String]
            | CompiledEpicPragma QName String
            | EtaPragma QName
  deriving (Typeable, Data, Show)

data LetBinding = LetBind LetInfo Relevance Name Expr Expr    -- ^ LetBind info name type defn
                | LetApply ModuleInfo ModuleName [TypedBindings] ModuleName [NamedArg Expr] (Map QName QName) (Map ModuleName ModuleName)
                | LetOpen ModuleInfo ModuleName     -- ^ only for highlighting and abstractToConcrete
  deriving (Typeable, Data, Show)

-- | A definition without its type signature.
data Definition
	= FunDef     DefInfo QName [Clause]
	| DataDef    DefInfo QName [LamBinding] [Constructor]
	    -- ^ the 'LamBinding's are 'DomainFree' and binds the parameters of the datatype.
	| RecDef     DefInfo QName (Maybe Constructor) [LamBinding] Expr [Declaration]
	    -- ^ The 'Expr' gives the constructor type telescope, @(x1 : A1)..(xn : An) -> Prop@,
            --   and the optional name is the constructor's name.
        | ScopedDef ScopeInfo Definition
  deriving (Typeable, Data, Show)

-- | Only 'Axiom's.
type TypeSignature  = Declaration
type Constructor    = TypeSignature

-- | A lambda binding is either domain free or typed.
data LamBinding
	= DomainFree Hiding Name    -- ^ . @x@ or @{x}@
	| DomainFull TypedBindings  -- ^ . @(xs:e)@ or @{xs:e}@
  deriving (Typeable, Data, Show)

-- | Typed bindings with hiding information.
data TypedBindings = TypedBindings Range (Arg TypedBinding)
	    -- ^ . @(xs : e)@ or @{xs : e}@
  deriving (Typeable, Data, Show)

-- | A typed binding. Appears in dependent function spaces, typed lambdas, and
--   telescopes. I might be tempting to simplify this to only bind a single
--   name at a time. This would mean that we would have to typecheck the type
--   several times (@x,y:A@ vs. @x:A; y:A@). In most cases this wouldn't
--   really be a problem, but it's good principle to not do extra work unless
--   you have to.
data TypedBinding = TBind Range [Name] Expr
		  | TNoBind Expr
  deriving (Typeable, Data, Show)

type Telescope	= [TypedBindings]

-- | We could throw away @where@ clauses at this point and translate them to
--   @let@. It's not obvious how to remember that the @let@ was really a
--   @where@ clause though, so for the time being we keep it here.
data Clause	= Clause LHS RHS [Declaration]
  deriving (Typeable, Data, Show)
data RHS	= RHS Expr
		| AbsurdRHS
		| WithRHS QName [Expr] [Clause] -- ^ The 'QName' is the name of the with function.
                | RewriteRHS [QName] [Expr] RHS [Declaration]
                    -- ^ The 'QName's are the names of the generated with functions.
                    --   One for each 'Expr'.
                    --   The RHS shouldn't be another RewriteRHS
  deriving (Typeable, Data, Show)

data LHS	= LHS LHSInfo QName [NamedArg Pattern] [Pattern]
  deriving (Typeable, Data, Show)

-- | Parameterised over the type of dot patterns.
data Pattern' e	= VarP Name
		| ConP PatInfo AmbiguousQName [NamedArg (Pattern' e)]
		| DefP PatInfo QName          [NamedArg (Pattern' e)]  -- ^ defined pattern
		| WildP PatInfo
		| AsP PatInfo Name (Pattern' e)
		| DotP PatInfo e
		| AbsurdP PatInfo
		| LitP Literal
		| ImplicitP PatInfo	-- ^ generated at type checking for implicit arguments
  deriving (Typeable, Data, Show)

type Pattern = Pattern' Expr

{--------------------------------------------------------------------------
    Instances
 --------------------------------------------------------------------------}

instance Functor Pattern' where
    fmap f p = case p of
	VarP x	    -> VarP x
	ConP i c ps -> ConP i c $ (fmap . fmap . fmap . fmap) f ps
	DefP i c ps -> DefP i c $ (fmap . fmap . fmap . fmap) f ps
	LitP l	    -> LitP l
	AsP i x p   -> AsP i x $ fmap f p
	DotP i e    -> DotP i (f e)
	AbsurdP i   -> AbsurdP i
	WildP i	    -> WildP i
	ImplicitP i -> ImplicitP i

-- foldr should really take its arguments in a different order!
instance Foldable Pattern' where
    foldr f z p = case p of
	VarP _	    -> z
	ConP _ _ ps -> (foldrF . foldrF . foldrF . foldrF) f ps z
	DefP _ _ ps -> (foldrF . foldrF . foldrF . foldrF) f ps z
	LitP _	    -> z
	AsP _ _ p   -> foldr f z p
	DotP _ e    -> f e z
	AbsurdP _   -> z
	WildP _	    -> z
	ImplicitP _ -> z
	where
	    foldrF f = flip (foldr f)

instance Traversable Pattern' where
    traverse f p = case p of
	VarP x	    -> pure $ VarP x
	ConP i c ps -> ConP i c <$> (traverse . traverse . traverse . traverse) f ps
	DefP i c ps -> DefP i c <$> (traverse . traverse . traverse . traverse) f ps
	LitP l	    -> pure $ LitP l
	AsP i x p   -> AsP i x <$> traverse f p
	DotP i e    -> DotP i <$> f e
	AbsurdP i   -> pure $ AbsurdP i
	WildP i	    -> pure $ WildP i
	ImplicitP i -> pure $ ImplicitP i

instance HasRange LamBinding where
    getRange (DomainFree _ x) = getRange x
    getRange (DomainFull b)   = getRange b

instance HasRange TypedBindings where
    getRange (TypedBindings r _) = r

instance HasRange TypedBinding where
    getRange (TBind r _ _) = r
    getRange (TNoBind e)   = getRange e

instance HasRange Expr where
    getRange (Var x)		= getRange x
    getRange (Def x)		= getRange x
    getRange (Con x)		= getRange x
    getRange (Lit l)		= getRange l
    getRange (QuestionMark i)	= getRange i
    getRange (Underscore  i)	= getRange i
    getRange (App i _ _)	= getRange i
    getRange (WithApp i _ _)	= getRange i
    getRange (Lam i _ _)	= getRange i
    getRange (AbsurdLam i _)    = getRange i
    getRange (Pi i _ _)		= getRange i
    getRange (Fun i _ _)	= getRange i
    getRange (Set i _)		= getRange i
    getRange (Prop i)		= getRange i
    getRange (Let i _ _)	= getRange i
    getRange (Rec i _)		= getRange i
    getRange (ETel tel)         = getRange tel
    getRange (ScopedExpr _ e)	= getRange e
    getRange (QuoteGoal _ _ e)	= getRange e
    getRange (Quote i)  	= getRange i
    getRange (DontCare)         = noRange

instance HasRange Declaration where
    getRange (Axiom      i _ _ _       ) = getRange i
    getRange (Field      i _ _         ) = getRange i
    getRange (Definition i _ _	       ) = getRange i
    getRange (Section    i _ _ _       ) = getRange i
    getRange (Apply	 i _ _ _ _ _ _ ) = getRange i
    getRange (Import     i _	       ) = getRange i
    getRange (Primitive  i _ _	       ) = getRange i
    getRange (Pragma	 i _	       ) = getRange i
    getRange (Open       i _           ) = getRange i
    getRange (ScopedDecl _ d	       ) = getRange d

instance HasRange Definition where
    getRange (FunDef  i _ _    )   = getRange i
    getRange (DataDef i _ _ _  )   = getRange i
    getRange (RecDef  i _ _ _ _ _) = getRange i
    getRange (ScopedDef _ d)       = getRange d

instance HasRange (Pattern' e) where
    getRange (VarP x)	   = getRange x
    getRange (ConP i _ _)  = getRange i
    getRange (DefP i _ _)  = getRange i
    getRange (WildP i)	   = getRange i
    getRange (ImplicitP i) = getRange i
    getRange (AsP i _ _)   = getRange i
    getRange (DotP i _)    = getRange i
    getRange (AbsurdP i)   = getRange i
    getRange (LitP l)	   = getRange l

instance HasRange LHS where
    getRange (LHS i _ _ _) = getRange i

instance HasRange Clause where
    getRange (Clause lhs rhs ds) = getRange (lhs,rhs,ds)

instance HasRange RHS where
    getRange AbsurdRHS                = noRange
    getRange (RHS e)                  = getRange e
    getRange (WithRHS _ e cs)         = fuseRange e cs
    getRange (RewriteRHS _ es rhs wh) = getRange (es, rhs, wh)

instance HasRange LetBinding where
    getRange (LetBind  i _ _ _ _     ) = getRange i
    getRange (LetApply i _ _ _ _ _ _ ) = getRange i
    getRange (LetOpen  i _           ) = getRange i

instance KillRange LamBinding where
  killRange (DomainFree h x) = killRange1 (DomainFree h) x
  killRange (DomainFull b)   = killRange1 DomainFull b

instance KillRange TypedBindings where
  killRange (TypedBindings r b) = TypedBindings (killRange r) (killRange b)

instance KillRange TypedBinding where
  killRange (TBind r xs e) = killRange3 TBind r xs e
  killRange (TNoBind e)    = killRange1 TNoBind e

instance KillRange Expr where
  killRange (Var x)          = killRange1 Var x
  killRange (Def x)          = killRange1 Def x
  killRange (Con x)          = killRange1 Con x
  killRange (Lit l)          = killRange1 Lit l
  killRange (QuestionMark i) = killRange1 QuestionMark i
  killRange (Underscore  i)  = killRange1 Underscore i
  killRange (App i e1 e2)    = killRange3 App i e1 e2
  killRange (WithApp i e es) = killRange3 WithApp i e es
  killRange (Lam i b e)      = killRange3 Lam i b e
  killRange (AbsurdLam i h)  = killRange1 AbsurdLam i h
  killRange (Pi i a b)       = killRange3 Pi i a b
  killRange (Fun i a b)      = killRange3 Fun i a b
  killRange (Set i n)        = Set (killRange i) n
  killRange (Prop i)         = killRange1 Prop i
  killRange (Let i ds e)     = killRange3 Let i ds e
  killRange (Rec i fs)       = Rec (killRange i) (map (id -*- killRange) fs)
  killRange (ETel tel)       = killRange1 ETel tel
  killRange (ScopedExpr s e) = killRange1 (ScopedExpr s) e
  killRange (QuoteGoal i x e)= killRange3 QuoteGoal i x e
  killRange (Quote i)        = killRange1 Quote i
  killRange (DontCare)       = DontCare

instance KillRange Relevance where
  killRange rel = rel -- no range to kill

instance KillRange Declaration where
  killRange (Axiom      i rel a b     ) = killRange4 Axiom      i rel a b
  killRange (Field      i a b         ) = killRange3 Field      i a b
  killRange (Definition i a b         ) = killRange3 Definition i a b
  killRange (Section    i a b c       ) = killRange4 Section    i a b c
  killRange (Apply      i a b c d e f ) = killRange5 Apply      i a b c d e f
   -- the last two arguments of Apply are name maps, so nothing to kill
  killRange (Import     i a           ) = killRange2 Import     i a
  killRange (Primitive  i a b         ) = killRange3 Primitive  i a b
  killRange (Pragma     i a           ) = Pragma (killRange i) a
  killRange (Open       i x           ) = killRange2 Open       i x
  killRange (ScopedDecl a d           ) = killRange1 (ScopedDecl a) d

instance KillRange Definition where
  killRange (FunDef  i a b    )   = killRange3 FunDef  i a b
  killRange (DataDef i a b c)     = killRange4 DataDef i a b c
  killRange (RecDef  i a b c d e) = killRange6 RecDef  i a b c d e
  killRange (ScopedDef s a)       = killRange1 (ScopedDef s) a

instance KillRange e => KillRange (Pattern' e) where
  killRange (VarP x)      = killRange1 VarP x
  killRange (ConP i a b)  = killRange3 ConP i a b
  killRange (DefP i a b)  = killRange3 DefP i a b
  killRange (WildP i)     = killRange1 WildP i
  killRange (ImplicitP i) = killRange1 ImplicitP i
  killRange (AsP i a b)   = killRange3 AsP i a b
  killRange (DotP i a)    = killRange2 DotP i a
  killRange (AbsurdP i)   = killRange1 AbsurdP i
  killRange (LitP l)      = killRange1 LitP l

instance KillRange LHS where
  killRange (LHS i a b c) = killRange4 LHS i a b c

instance KillRange Clause where
  killRange (Clause lhs rhs ds) = killRange3 Clause lhs rhs ds

instance KillRange RHS where
  killRange AbsurdRHS                = AbsurdRHS
  killRange (RHS e)                  = killRange1 RHS e
  killRange (WithRHS q e cs)         = killRange3 WithRHS q e cs
  killRange (RewriteRHS x es rhs wh) = killRange4 RewriteRHS x es rhs wh

instance KillRange LetBinding where
  killRange (LetBind  i rel a b c   ) = killRange5 LetBind  i rel a b c
  killRange (LetApply i a b c d e f ) = killRange5 LetApply i a b c d e f
  killRange (LetOpen  i x           ) = killRange2 LetOpen  i x

------------------------------------------------------------------------
-- Queries
------------------------------------------------------------------------

-- | Extracts all the names which are declared in a 'Declaration'.
-- This does not include open public or let expressions, but it does
-- include local modules and where clauses.

allNames :: Declaration -> Seq QName
allNames (Axiom     _ _ q _)   = Seq.singleton q
allNames (Field     _   q _)   = Seq.singleton q
allNames (Primitive _   q _)   = Seq.singleton q
allNames (Definition _ _ defs) = Fold.foldMap allNamesD defs
  where
  allNamesD :: Definition -> Seq QName
  allNamesD (FunDef _ q cls)         = q <| Fold.foldMap allNamesC cls
  allNamesD (DataDef _ q _ decls)    = q <| Fold.foldMap allNames decls
  allNamesD (ScopedDef _ def)        = allNamesD def
  allNamesD (RecDef _ q c _ _ decls) =
    q <| Fold.foldMap allNames c >< Fold.foldMap allNames decls

  allNamesC :: Clause -> Seq QName
  allNamesC (Clause _ rhs decls) = allNamesR rhs ><
                                   Fold.foldMap allNames decls

  allNamesR :: RHS -> Seq QName
  allNamesR RHS {}                = Seq.empty
  allNamesR AbsurdRHS {}          = Seq.empty
  allNamesR (WithRHS q _ cls)     = q <| Fold.foldMap allNamesC cls
  allNamesR (RewriteRHS qs _ rhs cls) =
    Seq.fromList qs >< allNamesR rhs
                    >< Fold.foldMap allNames cls
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
