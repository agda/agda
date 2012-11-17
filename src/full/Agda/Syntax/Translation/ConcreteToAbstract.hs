{-# LANGUAGE CPP, MultiParamTypeClasses, FunctionalDependencies,
             FlexibleInstances, UndecidableInstances, OverlappingInstances,
             ScopedTypeVariables
  #-}

{-| Translation from "Agda.Syntax.Concrete" to "Agda.Syntax.Abstract". Involves scope analysis,
    figuring out infix operator precedences and tidying up definitions.
-}
module Agda.Syntax.Translation.ConcreteToAbstract
    ( ToAbstract(..), localToAbstract
    , concreteToAbstract_
    , concreteToAbstract
    , NewModuleQName(..)
    , OldName(..)
    , TopLevel(..)
    , TopLevelInfo(..)
    , topLevelModuleName
    , AbstractRHS
    , NewModuleName, OldModuleName
    , NewName, OldQName
    , LeftHandSide, RightHandSide
    , PatName, APatName, LetDef, LetDefs
    ) where

import Prelude hiding (mapM)
import Control.Applicative
import Control.Monad.Reader hiding (mapM)
import Control.Monad.Error hiding (mapM)
import Data.Typeable
import Data.Traversable (mapM, traverse)
import Data.List ((\\), nub, foldl')
import qualified Data.Map as Map

import Agda.Syntax.Concrete as C hiding (topLevelModuleName)
import Agda.Syntax.Concrete.Operators
-- import qualified Agda.Syntax.Concrete.Copatterns as Cop -- merged into Operators
import Agda.Syntax.Abstract as A
import Agda.Syntax.Abstract.Copatterns
import Agda.Syntax.Position
import Agda.Syntax.Common
import Agda.Syntax.Info
import Agda.Syntax.Concrete.Definitions as C
import Agda.Syntax.Concrete.Pretty
import Agda.Syntax.Abstract.Pretty
import Agda.Syntax.Fixity
import Agda.Syntax.Notation
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad

import Agda.TypeChecking.Monad.Base (TypeError(..), Call(..), typeError,
                                     TCErr(..), extendlambdaname)
import Agda.TypeChecking.Monad.Trace (traceCall, traceCallCPS, setCurrentRange)
import Agda.TypeChecking.Monad.State
import Agda.TypeChecking.Monad.Options

import {-# SOURCE #-} Agda.Interaction.Imports (scopeCheckImport)
import Agda.Interaction.Options

import Agda.Utils.Monad
import Agda.Utils.Tuple
import Agda.Utils.List
import Agda.Utils.Fresh
import Agda.Utils.Pretty

#include "../../undefined.h"
import Agda.Utils.Impossible
import Agda.ImpossibleTest (impossibleTest)

{--------------------------------------------------------------------------
    Exceptions
 --------------------------------------------------------------------------}

notAModuleExpr e            = typeError $ NotAModuleExpr e
notAnExpression e           = typeError $ NotAnExpression e
notAValidLetBinding d       = typeError $ NotAValidLetBinding d
nothingAppliedToHiddenArg e = typeError $ NothingAppliedToHiddenArg e
nothingAppliedToInstanceArg e = typeError $ NothingAppliedToInstanceArg e

-- Debugging

printLocals :: Int -> String -> ScopeM ()
printLocals v s = verboseS "scope.top" v $ do
  locals <- getLocalVars
  reportSLn "" 0 $ s ++ " " ++ show locals

printScope :: String -> Int -> String -> ScopeM ()
printScope tag v s = verboseS ("scope." ++ tag) v $ do
  scope <- getScope
  reportSDoc "" 0 $ return $ vcat [ text s, text $ show scope ]

{--------------------------------------------------------------------------
    Helpers
 --------------------------------------------------------------------------}

annotateDecl :: ScopeM A.Declaration -> ScopeM A.Declaration
annotateDecl m = annotateDecls $ (:[]) <$> m

annotateDecls :: ScopeM [A.Declaration] -> ScopeM A.Declaration
annotateDecls m = do
  ds <- m
  s  <- getScope
  return $ ScopedDecl s ds

annotateExpr :: ScopeM A.Expr -> ScopeM A.Expr
annotateExpr m = do
  e <- m
  s <- getScope
  return $ ScopedExpr s e

expandEllipsis :: C.Pattern -> [C.Pattern] -> C.Clause -> C.Clause
expandEllipsis _ _ c@(C.Clause _ C.LHS{} _ _ _) = c
expandEllipsis p ps (C.Clause x (C.Ellipsis _ ps' eqs es) rhs wh wcs) =
  C.Clause x (C.LHS p (ps ++ ps') eqs es) rhs wh wcs

-- | Make sure that each variable occurs only once.
checkPatternLinearity :: [A.Pattern' e] -> ScopeM ()
checkPatternLinearity ps = case xs \\ nub xs of
    []  -> return ()
    ys  -> typeError $ RepeatedVariablesInPattern $ nub ys
  where
    xs = concatMap vars ps
    vars :: A.Pattern' e -> [C.Name]
    vars p = case p of
      A.VarP x               -> [nameConcrete x]
      A.ConP _ _ args        -> concatMap (vars . namedArg) args
      A.WildP _              -> []
      A.AsP _ x p            -> nameConcrete x : vars p
      A.DotP _ _             -> []
      A.AbsurdP _            -> []
      A.LitP _               -> []
      A.DefP _ _ args        -> concatMap (vars . namedArg) args
        -- Projection pattern, @args@ should be empty unless we have
        -- indexed records.
      A.ImplicitP _          -> __IMPOSSIBLE__
      A.PatternSynP _ _ args -> concatMap (vars . namedArg) args

-- | Compute the type of the record constructor (with bogus target type)
recordConstructorType :: [NiceDeclaration] -> C.Expr
recordConstructorType fields = build fs
  where
    fs = reverse $ dropWhile notField $ reverse fields

    notField NiceField{} = False
    notField _           = True

    build (NiceField r f _ _ x (Arg h rel e) : fs) =
        C.Pi [C.TypedBindings r $ Arg h rel (C.TBind r [BName x f] e)] $ build fs
      where r = getRange x
    build (d : fs)                     = C.Let noRange [killRange $ notSoNiceDeclaration d] $
                                           build fs
    build []                           = C.SetN noRange 0 -- todo: nicer

checkModuleApplication (C.SectionApp _ tel e) m0 x dir' =
  withCurrentModule m0 $ do
    (m, args) <- case appView e of
      AppView (Ident m) args -> return (m, args)
      _                      -> notAModuleExpr e

    tel' <- toAbstract tel
    (m1,args') <- toAbstract (OldModuleName m
                             , args
                             )
    s  <- getNamedScope m1
    -- Drop constructors (OnlyQualified) if there are arguments. The record constructor
    -- isn't properly in the record module, so copying it will lead to badness.
    let noRecConstr | null args = id
                    | otherwise = removeOnlyQualified
    (s', (renM, renD)) <- copyScope m0 . noRecConstr =<< getNamedScope m1
    s' <- applyImportDirectiveM (C.QName x) dir' s'
    modifyCurrentScope $ const s'
    printScope "mod.inst" 20 "copied source module"
    reportSLn "scope.mod.inst" 30 $ "renamings:\n  " ++ show renD ++ "\n  " ++ show renM
    return ((A.SectionApp tel' m1 args'), renD, renM)
checkModuleApplication (C.RecordModuleIFS _ recN) m0 x dir' =
  withCurrentModule m0 $ do
    m1 <- toAbstract $ OldModuleName recN
    s <- getNamedScope m1
    (s', (renM, renD)) <- copyScope m0 s
    s' <- applyImportDirectiveM recN dir' s'
    modifyCurrentScope $ const s'

    printScope "mod.inst" 20 "copied record module"
    return ((A.RecordModuleIFS m1), renD, renM)

checkModuleMacro apply r p x modapp open dir = withLocalVars $ do
    notPublicWithoutOpen open dir

    m0 <- toAbstract (NewModuleName x)

    printScope "mod.inst" 20 "module macro"

    -- If we're opening, the import directive is applied to the open,
    -- otherwise to the module itself.
    let dir' = case open of
                DontOpen  -> dir
                DoOpen    -> defaultImportDir

    (modapp', renD, renM) <- checkModuleApplication modapp m0 x dir'
    bindModule p x m0
    printScope "mod.inst.copy.after" 20 "after copying"
    case open of
      DoOpen   -> openModule_ (C.QName x) dir
      DontOpen -> return ()
    printScope "mod.inst" 20 $ show open
    stripNoNames
    printScope "mod.inst" 10 $ "after stripping"
    return [ apply info (m0 `withRangesOf` [x]) modapp' renD renM ]
  where
    info = ModuleInfo
             { minfoRange  = r
             , minfoAsName = Nothing
             , minfoAsTo   = renamingRange dir
             , minfoOpenShort = Just open
             , minfoDirective = Just dir
             }

-- | The @public@ keyword must only be used together with @open@.

notPublicWithoutOpen :: OpenShortHand -> ImportDirective -> ScopeM ()
notPublicWithoutOpen DoOpen   dir = return ()
notPublicWithoutOpen DontOpen dir = when (publicOpen dir) $ typeError $
  GenericError
    "The public keyword must only be used together with the open keyword"

-- | Computes the range of all the \"to\" keywords used in a renaming
-- directive.

renamingRange = getRange . map renToRange . renaming

{--------------------------------------------------------------------------
    Translation
 --------------------------------------------------------------------------}

concreteToAbstract_ :: ToAbstract c a => c -> ScopeM a
concreteToAbstract_ x = toAbstract x

concreteToAbstract :: ToAbstract c a => ScopeInfo -> c -> ScopeM a
concreteToAbstract scope x = withScope_ scope (toAbstract x)

-- | Things that can be translated to abstract syntax are instances of this
--   class.
class ToAbstract concrete abstract | concrete -> abstract where
    toAbstract    :: concrete -> ScopeM abstract

-- | This function should be used instead of 'toAbstract' for things that need
--   to keep track of precedences to make sure that we don't forget about it.
toAbstractCtx :: ToAbstract concrete abstract =>
                 Precedence -> concrete -> ScopeM abstract
toAbstractCtx ctx c = withContextPrecedence ctx $ toAbstract c

setContextCPS :: Precedence -> (a -> ScopeM b) ->
                 ((a -> ScopeM b) -> ScopeM b) -> ScopeM b
setContextCPS p ret f = do
  p' <- getContextPrecedence
  withContextPrecedence p $ f $ withContextPrecedence p' . ret

localToAbstractCtx :: ToAbstract concrete abstract =>
                     Precedence -> concrete -> (abstract -> ScopeM a) -> ScopeM a
localToAbstractCtx ctx c ret = setContextCPS ctx ret (localToAbstract c)

-- | This operation does not affect the scope, i.e. the original scope
--   is restored upon completion.
localToAbstract :: ToAbstract c a => c -> (a -> ScopeM b) -> ScopeM b
localToAbstract x ret = fst <$> localToAbstract' x ret

-- | Like 'localToAbstract' but returns the scope after the completion of the
--   second argument.
localToAbstract' :: ToAbstract c a => c -> (a -> ScopeM b) -> ScopeM (b, ScopeInfo)
localToAbstract' x ret = do
  scope <- getScope
  withScope scope $ ret =<< toAbstract x

instance (ToAbstract c1 a1, ToAbstract c2 a2) => ToAbstract (c1,c2) (a1,a2) where
  toAbstract (x,y) =
    (,) <$> toAbstract x <*> toAbstract y

instance (ToAbstract c1 a1, ToAbstract c2 a2, ToAbstract c3 a3) =>
         ToAbstract (c1,c2,c3) (a1,a2,a3) where
    toAbstract (x,y,z) = flatten <$> toAbstract (x,(y,z))
        where
            flatten (x,(y,z)) = (x,y,z)

instance ToAbstract c a => ToAbstract [c] [a] where
    toAbstract = mapM toAbstract

instance ToAbstract c a => ToAbstract (Maybe c) (Maybe a) where
    toAbstract Nothing  = return Nothing
    toAbstract (Just x) = Just <$> toAbstract x

-- Names ------------------------------------------------------------------

newtype NewName a = NewName a
newtype OldQName  = OldQName C.QName
newtype OldName   = OldName C.Name
newtype PatName   = PatName C.QName

instance ToAbstract (NewName C.Name) A.Name where
  toAbstract (NewName x) = do
    y <- freshAbstractName_ x
    bindVariable x y
    return y

instance ToAbstract (NewName C.BoundName) A.Name where
  toAbstract (NewName (BName x fx)) = do
    y <- freshAbstractName fx x
    bindVariable x y
    return y

nameExpr :: AbstractName -> A.Expr
nameExpr d = mk (anameKind d) $ anameName d
  where
    mk DefName        = Def
    mk FldName        = Def
    mk ConName        = Con . AmbQ . (:[])
    mk PatternSynName = A.PatternSyn

instance ToAbstract OldQName A.Expr where
  toAbstract (OldQName x) = do
    qx <- resolveName x
    reportSLn "scope.name" 10 $ "resolved " ++ show x ++ ": " ++ show qx
    case qx of
      VarName x'          -> return $ A.Var x'
      DefinedName _ d     -> return $ nameExpr d
      FieldName     d     -> return $ nameExpr d
      ConstructorName ds  -> return $ A.Con $ AmbQ (map anameName ds)
      UnknownName         -> notInScope x
      PatternSynResName d -> return $ nameExpr d

data APatName = VarPatName A.Name
              | ConPatName [AbstractName]
              | PatternSynPatName AbstractName

instance ToAbstract PatName APatName where
  toAbstract (PatName x) = do
    reportSLn "scope.pat" 10 $ "checking pattern name: " ++ show x
    rx <- resolveName x
    z  <- case (rx, x) of
      -- TODO: warn about shadowing
      (VarName y,       C.QName x)                          -> return $ Left x -- typeError $ RepeatedVariableInPattern y x
      (FieldName d,     C.QName x)                          -> return $ Left x
      (DefinedName _ d, C.QName x) | DefName == anameKind d -> return $ Left x
      (UnknownName,     C.QName x)                          -> return $ Left x
      (ConstructorName ds, _)                               -> return $ Right (Left ds)
      (PatternSynResName d, _)                              -> return $ Right (Right d)
      _                                                     ->
        typeError $ GenericError $
          "Cannot pattern match on " ++ show x ++ ", because it is not a constructor"
    case z of
      Left x  -> do
        reportSLn "scope.pat" 10 $ "it was a var: " ++ show x
        p <- VarPatName <$> toAbstract (NewName x)
        printLocals 10 "bound it:"
        return p
      Right (Left ds) -> do
        reportSLn "scope.pat" 10 $ "it was a con: " ++ show (map anameName ds)
        return $ ConPatName ds
      Right (Right d) -> do
        reportSLn "scope.pat" 10 $ "it was a pat syn: " ++ show (anameName d)
        return $ PatternSynPatName d


-- Should be a defined name.
instance ToAbstract OldName A.QName where
  toAbstract (OldName x) = do
    rx <- resolveName (C.QName x)
    case rx of
      DefinedName _ d -> return $ anameName d
      _               -> error $ show x ++ " - " ++ show rx

newtype NewModuleName      = NewModuleName      C.Name
newtype NewModuleQName     = NewModuleQName     C.QName
newtype OldModuleName      = OldModuleName      C.QName

freshQModule :: A.ModuleName -> C.Name -> ScopeM A.ModuleName
freshQModule m x = A.qualifyM m . mnameFromList . (:[]) <$> freshAbstractName_ x

checkForModuleClash :: C.Name -> ScopeM ()
checkForModuleClash x = do
  ms <- scopeLookup (C.QName x) <$> getScope
  unless (null ms) $ do
    reportSLn "scope.clash" 20 $ "clashing modules ms = " ++ show ms
    setCurrentRange (getRange x) $
      typeError $ ShadowedModule x $
                map ((`withRangeOf` x) . amodName) ms

instance ToAbstract NewModuleName A.ModuleName where
  toAbstract (NewModuleName x) = do
    checkForModuleClash x
    m <- getCurrentModule
    y <- freshQModule m x
    createModule False y
    return y

instance ToAbstract NewModuleQName A.ModuleName where
  toAbstract (NewModuleQName m) = toAbs noModuleName m
    where
      toAbs m (C.QName x)  = do
        y <- freshQModule m x
        createModule False y
        return y
      toAbs m (C.Qual x q) = do
        m' <- freshQModule m x
        toAbs m' q

instance ToAbstract OldModuleName A.ModuleName where
  toAbstract (OldModuleName q) = amodName <$> resolveModule q

-- Expressions ------------------------------------------------------------

-- | Peel off 'C.HiddenArg' and represent it as an 'NamedArg'.
mkNamedArg :: C.Expr -> NamedArg C.Expr
mkNamedArg (C.HiddenArg _ e) = Arg Hidden    Relevant e
mkNamedArg (C.InstanceArg _ e) = Arg Instance    Relevant e
mkNamedArg e                 = Arg NotHidden Relevant $ unnamed e

-- | Peel off 'C.HiddenArg' and represent it as an 'Arg', throwing away any name.
mkArg' :: Relevance -> C.Expr -> Arg C.Expr
mkArg' r (C.HiddenArg _ e) = Arg Hidden    r $ namedThing e
mkArg' r (C.InstanceArg _ e) = Arg Instance    r $ namedThing e
mkArg' r e                 = Arg NotHidden r e

-- | By default, arguments are @Relevant@.
mkArg :: C.Expr -> Arg C.Expr
-- mkArg (C.Dot _ e) = mkArg' Irrelevant e
mkArg e           = mkArg' Relevant e


-- | Parse a possibly dotted C.Expr as A.Expr.  Bool = True if dotted.
toAbstractDot :: Precedence -> C.Expr -> ScopeM (A.Expr, Bool)
toAbstractDot prec e = do
    reportSLn "scope.irrelevance" 100 $ "toAbstractDot: " ++ (render $ pretty e)
    traceCall (ScopeCheckExpr e) $ case e of
    -- annotateExpr e = ScopedExpr <scope from Monad> e
      C.Dot _ e -> do
        e <- toAbstractCtx prec e
        return (e, True)

      C.RawApp r es -> do
        e <- parseApplication es
        toAbstractDot prec e

      C.Paren _ e -> toAbstractDot TopCtx e

      e -> do
        e <- toAbstractCtx prec e
        return (e, False)

toAbstractOpArg :: Precedence -> OpApp C.Expr -> ScopeM A.Expr
toAbstractOpArg ctx (Ordinary e) = toAbstractCtx ctx e
toAbstractOpArg ctx (SyntaxBindingLambda r bs e) = toAbstractLam r bs e ctx

toAbstractLam :: Range -> [C.LamBinding] -> C.Expr -> Precedence -> ScopeM A.Expr
toAbstractLam r bs e ctx = do
        localToAbstract (map makeDomainFull bs) $ \bs ->
          case bs of
            b:bs' -> do
              e        <- toAbstractCtx ctx e
              let info = ExprRange r
              return $ A.Lam info b $ foldr mkLam e bs'
              where
                  mkLam b e = A.Lam (ExprRange $ fuseRange b e) b e
            [] -> __IMPOSSIBLE__


instance ToAbstract C.Expr A.Expr where
  toAbstract e =
    traceCall (ScopeCheckExpr e) $ annotateExpr $ case e of
    -- annotateExpr e = ScopedExpr <scope from Monad> e

  -- Names
      Ident x -> toAbstract (OldQName x)

  -- Literals
      C.Lit l -> return $ A.Lit l

  -- Meta variables
      C.QuestionMark r n -> do
        scope <- getScope
        return $ A.QuestionMark $ MetaInfo
                    { metaRange  = r
                    , metaScope  = scope
                    , metaNumber = n
                    , metaNameSuggestion = ""
                    }
      C.Underscore r n -> do
        scope <- getScope
        return $ A.Underscore $ MetaInfo
                    { metaRange  = r
                    , metaScope  = scope
                    , metaNumber = maybe Nothing __IMPOSSIBLE__ n
                    , metaNameSuggestion = maybe "" id n
                    }

  -- Raw application
      C.RawApp r es -> do
        e <- parseApplication es
        toAbstract e

{- Andreas, 2010-09-06 STALE COMMENT
  -- Dots are used in dot patterns and in irrelevant function space .A n -> B
  -- we propagate dots out from the head of applications

      C.Dot r e1 -> do
        t1 <- toAbstract e1
        return $ A.Dot t1
-}

  -- Application
      C.App r e1 e2 -> do
        e1 <- toAbstractCtx FunctionCtx e1
        e2 <- toAbstractCtx ArgumentCtx e2
        return $ A.App (ExprRange r) e1 e2

  -- Operator application
      C.OpApp r op es -> toAbstractOpApp op es

  -- With application
      C.WithApp r e es -> do
        e  <- toAbstractCtx WithFunCtx e
        es <- mapM (toAbstractCtx WithArgCtx) es
        return $ A.WithApp (ExprRange r) e es

  -- Malplaced hidden argument
      C.HiddenArg _ _ -> nothingAppliedToHiddenArg e
      C.InstanceArg _ _ -> nothingAppliedToInstanceArg e

  -- Lambda
      C.AbsurdLam r h -> return $ A.AbsurdLam (ExprRange r) h

      C.Lam r bs e -> toAbstractLam r bs e TopCtx

  -- Extended Lambda
      C.ExtendedLam r cs -> do
--        m <- getCurrentModule
        cname <- nextlamname r 0 extendlambdaname
        name  <- freshAbstractName_ cname
        reportSLn "toabstract.extendlambda" 10 $ "new extended lambda name: " ++ show name
        qname <- qualifyName_ name
        bindName PrivateAccess DefName cname qname
        let insertApp (C.RawAppP r es) = C.RawAppP r ((IdentP (C.QName cname)) : es)
            insertApp (C.IdentP q) = C.RawAppP (getRange q) ((IdentP (C.QName cname)) : [C.IdentP q])
            insertApp _ = __IMPOSSIBLE__
            insertHead (C.LHS p wps eqs with) = C.LHS (insertApp p) wps eqs with
            insertHead (C.Ellipsis r wps eqs with) = C.Ellipsis r wps eqs with
        scdef <- toAbstract (C.FunDef r [] defaultFixity' ConcreteDef True cname
                               (map (\(lhs,rhs,wh) -> -- wh = NoWhere, see parser for more info
                                      C.Clause cname (insertHead lhs) rhs wh []) cs))
        case scdef of
          (A.ScopedDecl si [A.FunDef di qname' NotDelayed cs]) -> do
            setScope si
            return $ A.ExtendedLam (ExprRange r) di qname' cs
          _ -> __IMPOSSIBLE__
          where
            nextlamname :: Range -> Int -> String -> ScopeM C.Name
            nextlamname r i s = do
              let cname_pre = C.Name r [Id $ s ++ show i]
              rn <- resolveName (C.QName cname_pre)
              case rn of
                UnknownName -> return $ cname_pre
                _           -> nextlamname r (i+1) s

-- Irrelevant non-dependent function type

      C.Fun r e1 e2 -> do
        Arg h rel (e0, dotted) <- traverse (toAbstractDot FunctionSpaceDomainCtx) $ mkArg e1
        let e1 = Arg h (if dotted then Irrelevant else rel) e0
        e2 <- toAbstractCtx TopCtx e2
        let info = ExprRange r
        return $ A.Fun info e1 e2

{-
-- Other function types

      C.Fun r e1 e2 -> do
        e1 <- toAbstractCtx FunctionSpaceDomainCtx $ mkArg e1
        e2 <- toAbstractCtx TopCtx e2
        let info = ExprRange r
        return $ A.Fun info e1 e2
-}

      e0@(C.Pi tel e) ->
        localToAbstract tel $ \tel -> do
        e    <- toAbstractCtx TopCtx e
        let info = ExprRange (getRange e0)
        return $ A.Pi info tel e

  -- Sorts
      C.Set _    -> return $ A.Set (ExprRange $ getRange e) 0
      C.SetN _ n -> return $ A.Set (ExprRange $ getRange e) n
      C.Prop _   -> return $ A.Prop $ ExprRange $ getRange e

  -- Let
      e0@(C.Let _ ds e) ->
        localToAbstract (LetDefs ds) $ \ds' -> do
        e        <- toAbstractCtx TopCtx e
        let info = ExprRange (getRange e0)
        return $ A.Let info ds' e

  -- Record construction
      C.Rec r fs  -> do
        let (xs, es) = unzip fs
        es <- toAbstractCtx TopCtx es
        return $ A.Rec (ExprRange r) $ zip xs es

  -- Record update
      C.RecUpdate r e fs -> do
        let (xs, es) = unzip fs
        e <- toAbstract e
        es <- toAbstractCtx TopCtx es
        return $ A.RecUpdate (ExprRange r) e $ zip xs es

  -- Parenthesis
      C.Paren _ e -> toAbstractCtx TopCtx e

  -- Pattern things
      C.Dot _ _  -> notAnExpression e
      C.As _ _ _ -> notAnExpression e
      C.Absurd _ -> notAnExpression e

  -- Impossible things
      C.ETel _   -> __IMPOSSIBLE__

  -- Quoting
      C.QuoteGoal _ x e -> do
        x' <- toAbstract (NewName x)
        e' <- toAbstract e
        return $ A.QuoteGoal (ExprRange $ getRange e) x' e'
      C.Quote r -> return $ A.Quote (ExprRange r)
      C.QuoteTerm r -> return $ A.QuoteTerm (ExprRange r)
      C.Unquote r -> return $ A.Unquote (ExprRange r)

  -- DontCare
      C.DontCare e -> A.DontCare <$> toAbstract e

instance ToAbstract C.LamBinding A.LamBinding where
  toAbstract (C.DomainFree h rel x) = A.DomainFree h rel <$> toAbstract (NewName x)
  toAbstract (C.DomainFull tb)      = A.DomainFull <$> toAbstract tb

makeDomainFull :: C.LamBinding -> C.LamBinding
makeDomainFull b@C.DomainFull{} = b
makeDomainFull (C.DomainFree h rel x) =
  C.DomainFull $ C.TypedBindings r $ Arg h rel $ C.TBind r [x] $ C.Underscore r Nothing
  where r = getRange x
instance ToAbstract C.TypedBindings A.TypedBindings where
  toAbstract (C.TypedBindings r bs) = A.TypedBindings r <$> toAbstract bs

instance ToAbstract C.TypedBinding A.TypedBinding where
  toAbstract (C.TBind r xs t) = do
    t' <- toAbstractCtx TopCtx t
    xs' <- toAbstract (map NewName xs)
    return $ A.TBind r xs' t'
  toAbstract (C.TNoBind e) = do
    e <- toAbstractCtx TopCtx e
    return (A.TNoBind e)

-- | Returns the scope inside the checked module.
scopeCheckModule :: Range -> C.QName -> A.ModuleName -> C.Telescope -> [C.Declaration] ->
                    ScopeM (ScopeInfo, [A.Declaration])
scopeCheckModule r x qm tel ds = do
  printScope "module" 20 $ "checking module " ++ show x
  res <- withCurrentModule qm $ do
    -- pushScope m
    -- qm <- getCurrentModule
    printScope "module" 20 $ "inside module " ++ show x
    withLocalVars $ do
      tel   <- toAbstract tel
      ds    <- (:[]) . A.Section info (qm `withRangesOfQ` x) tel <$>
                 toAbstract ds
      scope <- getScope
      return (scope, ds)

  -- Binding is done by the caller
  printScope "module" 20 $ "after module " ++ show x
  return res
  where
    info = ModuleInfo r noRange Nothing Nothing Nothing

newtype TopLevel a = TopLevel a

data TopLevelInfo = TopLevelInfo
        { topLevelDecls :: [A.Declaration]
        , outsideScope  :: ScopeInfo
        , insideScope   :: ScopeInfo
        }

-- | The top-level module name.

topLevelModuleName :: TopLevelInfo -> A.ModuleName
topLevelModuleName topLevel = scopeCurrent (insideScope topLevel)

-- Top-level declarations are always (import|open)* module
instance ToAbstract (TopLevel [C.Declaration]) TopLevelInfo where
    toAbstract (TopLevel ds) = case splitAt (length ds - 1) ds of
        (ds', [C.Module r m tel ds]) -> do
          setTopLevelModule m
          am           <- toAbstract (NewModuleQName m)
          ds'          <- toAbstract ds'
          (scope0, ds) <- scopeCheckModule r m am tel ds
          scope        <- getScope
          return $ TopLevelInfo (ds' ++ ds) scope scope0
        _ -> __IMPOSSIBLE__

-- | runs Syntax.Concrete.Definitions.niceDeclarations on main module
niceDecls :: [C.Declaration] -> ScopeM [NiceDeclaration]
niceDecls ds = case runNice $ niceDeclarations ds of
  Left e   -> throwError $ Exception (getRange e) (show e)
  Right ds -> return ds

instance ToAbstract [C.Declaration] [A.Declaration] where
  toAbstract ds = do
    -- don't allow to switch off termination checker in --safe mode
    ds <- ifM (optSafe <$> commandLineOptions) (mapM noNoTermCheck ds) (return ds)
    toAbstract =<< niceDecls ds
   where
    noNoTermCheck (C.Pragma (NoTerminationCheckPragma r)) =
      typeError $ SafeFlagNoTerminationCheck
    noNoTermCheck d = return d

newtype LetDefs = LetDefs [C.Declaration]
newtype LetDef = LetDef NiceDeclaration

instance ToAbstract LetDefs [A.LetBinding] where
  toAbstract (LetDefs ds) =
    concat <$> (toAbstract =<< map LetDef <$> niceDecls ds)

instance ToAbstract LetDef [A.LetBinding] where
    toAbstract (LetDef d) =
        case d of
            NiceMutual _ _ d@[C.FunSig _ fx _ rel _ x t, C.FunDef _ _ _ abstract _ _ [cl]] ->
                do  when (abstract == AbstractDef) $ do
                      typeError $ GenericError $ "abstract not allowed in let expressions"
                    e <- letToAbstract cl
                    t <- toAbstract t
                    x <- toAbstract (NewName $ C.BName x fx)
                    return [ A.LetBind (LetRange $ getRange d) rel x t e ]

            -- irrefutable let binding, like  (x , y) = rhs
            NiceFunClause r PublicAccess ConcreteDef termCheck d@(C.FunClause (C.LHS p [] [] []) (C.RHS rhs) NoWhere) -> do
              rhs <- toAbstract rhs
              p   <- parsePattern p
              p   <- toAbstract p
              checkPatternLinearity [p]
              p   <- toAbstract p
              return [ A.LetPatBind (LetRange r) p rhs ]

            -- You can't open public in a let
            NiceOpen r x dirs | not (C.publicOpen dirs) -> do
              m       <- toAbstract (OldModuleName x)
              n       <- length . scopeLocals <$> getScope
              openModule_ x dirs
              return [A.LetOpen (ModuleInfo
                                   { minfoRange  = r
                                   , minfoAsName = Nothing
                                   , minfoAsTo   = renamingRange dirs
                                   , minfoOpenShort = Nothing
                                   , minfoDirective = Just dirs
                                   })
                                m
                     ]

            NiceModuleMacro r p x modapp open dir | not (C.publicOpen dir) ->
              checkModuleMacro LetApply r p x modapp open dir

            _   -> notAValidLetBinding d
        where
            letToAbstract (C.Clause top clhs@(C.LHS p [] [] []) (C.RHS rhs) NoWhere []) = do
{-
                p    <- parseLHS top p
                localToAbstract (snd $ lhsArgs p) $ \args ->
-}
                (x, args) <- do
                  res <- parseLHS top p
                  case res of
                    C.LHSHead x args -> return (x, args)
                    C.LHSProj{} -> typeError $ GenericError $ "copatterns not allowed in let bindings"

                localToAbstract args $ \args ->
                    do  rhs <- toAbstract rhs
                        foldM lambda rhs (reverse args)  -- just reverse because these DomainFree
            letToAbstract _ = notAValidLetBinding d

            -- Named patterns not allowed in let definitions
            lambda e (Arg h rel (Named Nothing (A.VarP x))) = return $ A.Lam i (A.DomainFree h rel x) e
                where
                    i = ExprRange (fuseRange x e)
            lambda e (Arg h rel (Named Nothing (A.WildP i))) =
                do  x <- freshNoName (getRange i)
                    return $ A.Lam i' (A.DomainFree h rel x) e
                where
                    i' = ExprRange (fuseRange i e)
            lambda _ _ = notAValidLetBinding d

-- The only reason why we return a list is that open declarations disappears.
-- For every other declaration we get a singleton list.
instance ToAbstract NiceDeclaration A.Declaration where

  toAbstract d = annotateDecls $
    traceCall (ScopeCheckDeclaration d) $
    case d of

  -- Axiom
    C.Axiom r f p rel x t -> do
      -- check that we do not postulate in --safe mode
      clo <- commandLineOptions
      when (optSafe clo) (typeError (SafeFlagPostulate x))
      -- check the postulate
      toAbstractNiceAxiom d

  -- Fields
    C.NiceField r f p a x t -> do
      unless (p == PublicAccess) $ typeError $ GenericError "Record fields can not be private"
      t' <- toAbstractCtx TopCtx t
      y  <- freshAbstractQName f x
      irrProj <- optIrrelevantProjections <$> pragmaOptions
      unless (argRelevance t == Irrelevant && not irrProj) $
        -- Andreas, 2010-09-24: irrelevant fields are not in scope
        -- this ensures that projections out of irrelevant fields cannot occur
        -- Ulf: unless you turn on --irrelevant-projections
        bindName p FldName x y
      return [ A.Field (mkDefInfo x f p a r) y t' ]

  -- Primitive function
    PrimitiveFunction r f p a x t -> do
      t' <- toAbstractCtx TopCtx t
      y  <- freshAbstractQName f x
      bindName p DefName x y
      return [ A.Primitive (mkDefInfo x f p a r) y t' ]

  -- Definitions (possibly mutual)
    NiceMutual r termCheck ds -> do
      ds' <- toAbstract ds
      return [ A.Mutual (MutualInfo termCheck r) ds' ]

    C.NiceRecSig r f a x ls t -> withLocalVars $ do
        let toTypeBinding :: C.LamBinding -> C.TypedBindings
            toTypeBinding b = case makeDomainFull b of
               C.DomainFull b -> b
               _            -> __IMPOSSIBLE__
        ls' <- toAbstract (map toTypeBinding ls)
        x'  <- freshAbstractQName f x
        bindName a DefName x x'
        t' <- toAbstract t
        return [ A.RecSig (mkDefInfo x f a ConcreteDef r) x' ls' t' ]
    C.NiceDataSig r f a x ls t -> withLocalVars $ do
        printScope "scope.data.sig" 20 ("checking DataSig for " ++ show x)
        let toTypeBinding :: C.LamBinding -> C.TypedBindings
            toTypeBinding b = case makeDomainFull b of
               C.DomainFull b -> b
               _            -> __IMPOSSIBLE__
        ls' <- toAbstract (map toTypeBinding ls)
        x'  <- freshAbstractQName f x
        {- -- Andreas, 2012-01-16: remember number of parameters
        bindName a (DataName (length ls)) x x' -}
        bindName a DefName x x'
        t' <- toAbstract t
        return [ A.DataSig (mkDefInfo x f a ConcreteDef r) x' ls' t' ]
  -- Type signatures
    C.FunSig r f p rel tc x t -> toAbstractNiceAxiom (C.Axiom r f p rel x t)
  -- Function definitions
    C.FunDef r ds f a tc x cs -> do
        printLocals 10 $ "checking def " ++ show x
        (x',cs) <- toAbstract (OldName x,cs)
        (delayed, cs) <- translateCopatternClauses cs
        return [ A.FunDef (mkDefInfo x f PublicAccess a r) x' delayed cs ]

  -- Uncategorized function clauses
    C.NiceFunClause r acc abs termCheck (C.FunClause lhs rhs wcls) ->
      typeError $ GenericError $
        "Missing type signature for left hand side " ++ show lhs
    C.NiceFunClause{} -> __IMPOSSIBLE__

  -- Data definitions
    C.DataDef r f a x pars cons -> withLocalVars $ do
        printScope "scope.data.def" 20 ("checking DataDef for " ++ show x)
        -- Check for duplicate constructors
        do let cs   = map conName cons
               dups = nub $ cs \\ nub cs
               bad  = filter (`elem` dups) cs
           unless (distinct cs) $
             setCurrentRange (getRange bad) $
                typeError $ DuplicateConstructors dups

        pars <- toAbstract pars
        DefinedName p ax <- resolveName (C.QName x)
        let x' = anameName ax
        -- Create the module for the qualified constructors
        checkForModuleClash x -- disallow shadowing previously defined modules
        let m = mnameFromList $ qnameToList x'
        createModule True m
        bindModule p x m  -- make it a proper module
        cons <- toAbstract (map (ConstrDecl NoRec m a p) cons)
        -- Open the module
        -- openModule_ (C.QName x) defaultImportDir{ publicOpen = True }
        printScope "data" 20 $ "Checked data " ++ show x
        return [ A.DataDef (mkDefInfo x f PublicAccess a r) x' pars cons ]
      where
        conName (C.Axiom _ _ _ _ c _) = c
        conName _ = __IMPOSSIBLE__

  -- Record definitions (mucho interesting)
    C.RecDef r f a x ind cm pars fields ->
      withLocalVars $ do
        -- Check that the generated module doesn't clash with a previously
        -- defined module
        checkForModuleClash x
        pars   <- toAbstract pars
        DefinedName p ax <- resolveName (C.QName x)
        let x' = anameName ax
        contel <- toAbstract $ recordConstructorType fields
        m0     <- getCurrentModule
        let m = A.qualifyM m0 $ mnameFromList $ (:[]) $ last $ qnameToList x'
        printScope "rec" 15 "before record"
        createModule False m
        afields <- withCurrentModule m $ do
          afields <- toAbstract fields
          printScope "rec" 15 "checked fields"
          return afields
        bindModule p x m
        cm' <- mapM (\(ThingWithFixity c f) -> bindConstructorName m c f a p YesRec) cm
        printScope "rec" 15 "record complete"
        return [ A.RecDef (mkDefInfo x f PublicAccess a r) x' ind cm' pars contel afields ]

    -- Andreas, 2012-10-30 anonymous modules are like Coq sections
    NiceModule r p a (C.QName name) tel ds ->
      traceCall (ScopeCheckDeclaration $ NiceModule r p a (C.QName name) tel []) $ do
      (name, p, isSection) <- if not (C.isNoName name)
        then return (name, p, False)
        else do
          (i :: NameId) <- fresh
          return (C.NoName (getRange name) i, PrivateAccess, True)
      aname <- toAbstract (NewModuleName name)
      ds <- snd <$> scopeCheckModule r (C.QName name) aname tel ds
      bindModule p name aname
      -- if the module was anonymous open it public
      when isSection $
        openModule_ (C.QName name) $
          defaultImportDir { publicOpen = True }
      return ds

    NiceModule _ _ _ C.Qual{} _ _ -> __IMPOSSIBLE__

    NiceModuleMacro r p x modapp open dir ->
      checkModuleMacro Apply r p x modapp open dir

    NiceOpen r x dir -> do
      m <- toAbstract (OldModuleName x)
      printScope "open" 20 $ "opening " ++ show x
      openModule_ x dir
      printScope "open" 20 $ "result:"
      return [A.Open (ModuleInfo
                        { minfoRange  = r
                        , minfoAsName = Nothing
                        , minfoAsTo   = renamingRange dir
                        , minfoOpenShort = Nothing
                        , minfoDirective = Just dir
                        })
                     m]

    NicePragma r p -> do
      ps <- toAbstract p
      return $ map (A.Pragma r) ps

    NiceImport r x as open dir -> do
      notPublicWithoutOpen open dir

      -- First scope check the imported module and return its name and
      -- interface. This is done with that module as the top-level module.
      -- This is quite subtle. We rely on the fact that when setting the
      -- top-level module and generating a fresh module name the generated
      -- name will be exactly the same as the name generated when checking
      -- the imported module.
      (m, i) <- withCurrentModule noModuleName $ withTopLevelModule x $ do
        m <- toAbstract $ NewModuleQName x
        printScope "import" 10 "before import:"
        (m, i) <- scopeCheckImport m
        printScope "import" 10 $ "scope checked import: " ++ show i
        -- We don't want the top scope of the imported module (things happening
        -- before the module declaration)
        return (m, Map.delete noModuleName i)

      -- Merge the imported scopes with the current scopes
      modifyScopeInfo $ \s -> s { scopeModules = Map.unionWith mergeScope
                                                  (Map.delete m $ scopeModules s) i }

      -- Bind the desired module name to the right abstract name.
      case as of
        Nothing -> bindQModule PrivateAccess x m
        Just y  -> bindModule PrivateAccess (asName y) m

      printScope "import" 10 "merged imported sig:"

      -- Open if specified, otherwise apply import directives
      let (name, theAsSymbol, theAsName) = case as of
            Nothing -> (x,                  noRange,   Nothing)
            Just a  -> (C.QName (asName a), asRange a, Just (asName a))
      case open of
        DoOpen   -> do
          toAbstract [ C.Open r name dir ]
          return ()
        DontOpen -> do
          -- If not opening import directives are applied to the original scope
          modifyNamedScopeM m $ applyImportDirectiveM x dir
      return [ A.Import (ModuleInfo
                           { minfoRange  = r
                           , minfoAsName = theAsName
                           , minfoAsTo   =
                               getRange (theAsSymbol, renamingRange dir)
                           , minfoOpenShort = Just open
                           , minfoDirective = Just dir
                           })
                        m ]

    NicePatternSyn r fx n as p -> do
      reportSLn "scope.pat" 10 $ "found nice pattern syn: " ++ show r

      isparameterised <- not . null <$> getLocalVars
      when isparameterised $ typeError $ NotSupported
          "pattern synonym in parameterised module"

      y <- freshAbstractQName fx n
      bindName PublicAccess PatternSynName n y
      defn <- withLocalVars $ do
               p'   <- killRange <$> (toAbstract =<< toAbstract =<< parsePatternSyn p)
               as'  <- mapM (\a -> unVarName =<< resolveName (C.QName a)) as
               return (as', p')
      modifyPatternSyns (Map.insert y defn)
      return []
      where unVarName (VarName a) = return a
            unVarName _           = typeError $ UnusedVariableInPatternSynonym

    where
      -- checking postulate or type sig. without checking safe flag
      toAbstractNiceAxiom (C.Axiom r f p rel x t) = do
        t' <- toAbstractCtx TopCtx t
        y  <- freshAbstractQName f x
        bindName p DefName x y
        return [ A.Axiom (mkDefInfo x f p ConcreteDef r) rel y t' ]
      toAbstractNiceAxiom _ = __IMPOSSIBLE__


data IsRecordCon = YesRec | NoRec
data ConstrDecl = ConstrDecl IsRecordCon A.ModuleName IsAbstract Access C.NiceDeclaration

bindConstructorName m x f a p record = do
  -- The abstract name is the qualified one
  y <- withCurrentModule m $ freshAbstractQName f x
  -- Bind it twice, once unqualified and once qualified
  bindName p' ConName x y
  withCurrentModule m $ bindName p'' ConName x y
  return y
  where
    -- An abstract constructor is private (abstract constructor means
    -- abstract datatype, so the constructor should not be exported).
    p' = case a of
           AbstractDef -> PrivateAccess
           _           -> p
    p'' = case (a, record) of
            (AbstractDef, _) -> PrivateAccess
            (_, YesRec)      -> OnlyQualified   -- record constructors aren't really in the record module
            _                -> PublicAccess

instance ToAbstract ConstrDecl A.Declaration where
  toAbstract (ConstrDecl record m a p (C.Axiom r f _ rel x t)) = do -- rel==Relevant
    t' <- toAbstractCtx TopCtx t
    -- The abstract name is the qualified one
    -- Bind it twice, once unqualified and once qualified
    y <- bindConstructorName m x f a p record
    printScope "con" 15 "bound constructor"
    return $ A.Axiom (mkDefInfo x f p ConcreteDef r) rel y t'

  toAbstract _ = __IMPOSSIBLE__    -- a constructor is always an axiom

instance ToAbstract C.Pragma [A.Pragma] where
    toAbstract (C.ImpossiblePragma _) = impossibleTest
    toAbstract (C.OptionsPragma _ opts) = return [ A.OptionsPragma opts ]
    toAbstract (C.CompiledTypePragma _ x hs) = do
      e <- toAbstract $ OldQName x
      case e of
        A.Def x -> return [ A.CompiledTypePragma x hs ]
        _       -> fail $ "Bad compiled type: " ++ show x  -- TODO: error message
    toAbstract (C.CompiledDataPragma _ x hs hcs) = do
      e <- toAbstract $ OldQName x
      case e of
        A.Def x -> return [ A.CompiledDataPragma x hs hcs ]
        _       -> fail $ "Not a datatype: " ++ show x  -- TODO: error message
    toAbstract (C.CompiledPragma _ x hs) = do
      e <- toAbstract $ OldQName x
      y <- case e of
            A.Def x -> return x
            A.Con _ -> fail "Use COMPILED_DATA for constructors" -- TODO
            _       -> __IMPOSSIBLE__
      return [ A.CompiledPragma y hs ]
    toAbstract (C.CompiledEpicPragma _ x ep) = do
      e <- toAbstract $ OldQName x
      y <- case e of
            A.Def x -> return x
            _       -> __IMPOSSIBLE__
      return [ A.CompiledEpicPragma y ep ]
    toAbstract (C.CompiledJSPragma _ x ep) = do
      e <- toAbstract $ OldQName x
      y <- case e of
            A.Def x -> return x
            A.Con (AmbQ [x]) -> return x
            A.Con x -> fail ("COMPILED_JS used on ambiguous name " ++ show x)
            _       -> __IMPOSSIBLE__
      return [ A.CompiledJSPragma y ep ]
    toAbstract (C.StaticPragma _ x) = do
        e <- toAbstract $ OldQName x
        y <- case e of
            A.Def x -> return x
            _       -> __IMPOSSIBLE__
        return [ A.StaticPragma y ]
    toAbstract (C.BuiltinPragma _ b e) = do
        e <- toAbstract e
        return [ A.BuiltinPragma b e ]
    toAbstract (C.ImportPragma _ i) = do
      addHaskellImport i
      return []
    toAbstract (C.EtaPragma _ x) = do
      e <- toAbstract $ OldQName x
      case e of
        A.Def x -> return [ A.EtaPragma x ]
        _       -> fail "Bad ETA pragma"
    -- NO_TERMINATION_CHECK is handled by the nicifier
    toAbstract (C.NoTerminationCheckPragma _) = __IMPOSSIBLE__

instance ToAbstract C.Clause A.Clause where
    toAbstract (C.Clause top C.Ellipsis{} _ _ _) = fail "bad '...'" -- TODO: errors message
    toAbstract (C.Clause top lhs@(C.LHS p wps eqs with) rhs wh wcs) = withLocalVars $ do
-- WAS:     let wcs' = map (expandEllipsis p wps) wcs
      -- Andreas, 2012-02-14: need to reset local vars before checking subclauses
      vars <- getLocalVars
      let wcs' = map (\ c -> setLocalVars vars >> do return $ expandEllipsis p wps c) wcs
      lhs' <- toAbstract (LeftHandSide top p wps)
      printLocals 10 "after lhs:"
      let (whname, whds) = case wh of
            NoWhere        -> (Nothing, [])
            AnyWhere ds    -> (Nothing, ds)
            SomeWhere m ds -> (Just m, ds)
      if not (null eqs)
        then do
          rhs <- toAbstract =<< toAbstractCtx TopCtx (RightHandSide eqs with wcs' rhs whds)
          return $ A.Clause lhs' rhs []
        else do
          -- the right hand side is checked inside the module of the local definitions
          (rhs, ds) <- whereToAbstract (getRange wh) whname whds $
                        toAbstractCtx TopCtx (RightHandSide eqs with wcs' rhs [])
          rhs <- toAbstract rhs
          return $ A.Clause lhs' rhs ds

whereToAbstract :: Range -> Maybe C.Name -> [C.Declaration] -> ScopeM a -> ScopeM (a, [A.Declaration])
whereToAbstract _ _ [] inner = do
  x <- inner
  return (x, [])
whereToAbstract r whname whds inner = do
  m <- maybe (nameConcrete <$> freshNoName noRange) return whname
  let acc = maybe PrivateAccess (const PublicAccess) whname  -- unnamed where's are private
  let tel = []
  old <- getCurrentModule
  am  <- toAbstract (NewModuleName m)
  (scope, ds) <- scopeCheckModule r (C.QName m) am tel whds
  setScope scope
  x <- inner
  setCurrentModule old
  bindModule acc m am
  return (x, ds)

data RightHandSide = RightHandSide
  { rhsRewriteEqn :: [C.RewriteEqn]  -- ^ @rewrite e@ (many)
  , rhsWithExpr   :: [C.WithExpr]    -- ^ @with e@ (many)
  , rhsSubclauses :: [ScopeM C.Clause] -- ^ the subclauses spawned by a with (monadic because we need to reset the local vars before checking these clauses)
  , rhs           :: C.RHS
  , rhsWhereDecls :: [C.Declaration]
  }

data AbstractRHS = AbsurdRHS'
                 | WithRHS' [A.Expr] [ScopeM C.Clause]  -- ^ The with clauses haven't been translated yet
                 | RHS' A.Expr
                 | RewriteRHS' [A.Expr] AbstractRHS [A.Declaration]

qualifyName_ :: A.Name -> ScopeM A.QName
qualifyName_ x = do
  m <- getCurrentModule
  return $ A.qualify m x

withFunctionName :: String -> ScopeM A.QName
withFunctionName s = do
  NameId i _ <- fresh
  qualifyName_ =<< freshName_ (s ++ show i)

instance ToAbstract AbstractRHS A.RHS where
  toAbstract AbsurdRHS'            = return A.AbsurdRHS
  toAbstract (RHS' e)              = return $ A.RHS e
  toAbstract (RewriteRHS' eqs rhs wh) = do
    auxs <- replicateM (length eqs) $ withFunctionName "rewrite-"
    rhs  <- toAbstract rhs
    return $ RewriteRHS auxs eqs rhs wh
  toAbstract (WithRHS' es cs) = do
    aux <- withFunctionName "with-"
    A.WithRHS aux es <$> do toAbstract =<< sequence cs

instance ToAbstract RightHandSide AbstractRHS where
  toAbstract (RightHandSide eqs@(_:_) es cs rhs wh) = do
    eqs <- toAbstractCtx TopCtx eqs
                 -- TODO: remember named where
    (rhs, ds) <- whereToAbstract (getRange wh) Nothing wh $
                  toAbstract (RightHandSide [] es cs rhs [])
    return $ RewriteRHS' eqs rhs ds
  toAbstract (RightHandSide [] [] (_ : _) _ _)        = __IMPOSSIBLE__
  toAbstract (RightHandSide [] (_ : _) _ (C.RHS _) _) = typeError $ BothWithAndRHS
  toAbstract (RightHandSide [] [] [] rhs [])          = toAbstract rhs
  toAbstract (RightHandSide [] es cs C.AbsurdRHS [])  = do
    es <- toAbstractCtx TopCtx es
    return $ WithRHS' es cs
  -- TODO: some of these might be possible
  toAbstract (RightHandSide [] (_ : _) _ C.AbsurdRHS (_ : _)) = __IMPOSSIBLE__
  toAbstract (RightHandSide [] [] [] (C.RHS _) (_ : _))       = __IMPOSSIBLE__
  toAbstract (RightHandSide [] [] [] C.AbsurdRHS (_ : _))     = __IMPOSSIBLE__

instance ToAbstract C.RHS AbstractRHS where
    toAbstract C.AbsurdRHS = return $ AbsurdRHS'
    toAbstract (C.RHS e)   = RHS' <$> toAbstract e

data LeftHandSide = LeftHandSide C.Name C.Pattern [C.Pattern]

instance ToAbstract LeftHandSide A.LHS where
    toAbstract (LeftHandSide top lhs wps) =
      traceCall (ScopeCheckLHS top lhs) $ do
        lhscore <- parseLHS top lhs
        reportSLn "scope.lhs" 5 $ "parsed lhs: " ++ show lhscore
        printLocals 10 "before lhs:"
        -- error if copattern parsed but no --copatterns option
        haveCoPats <- optCopatterns <$> pragmaOptions
        unless haveCoPats $
          case lhscore of
            C.LHSHead x ps -> return ()
            C.LHSProj{} -> typeError $ NeedOptionCopatterns
        -- scope check patterns except for dot patterns
        lhscore <- toAbstract lhscore
        reportSLn "scope.lhs" 5 $ "parsed lhs patterns: " ++ show lhscore
        wps  <- toAbstract =<< mapM parsePattern wps
        checkPatternLinearity $ lhsCoreAllPatterns lhscore ++ wps
        printLocals 10 "checked pattern:"
        -- scope check dot patterns
        lhscore <- toAbstract lhscore
        reportSLn "scope.lhs" 5 $ "parsed lhs dot patterns: " ++ show lhscore
        wps     <- toAbstract wps
        printLocals 10 "checked dots:"
        return $ A.LHS (LHSRange $ getRange (lhs, wps)) lhscore wps

-- does not check pattern linearity
instance ToAbstract C.LHSCore (A.LHSCore' C.Expr) where
    toAbstract (C.LHSHead x ps) = do
        x    <- withLocalVars $ setLocalVars [] >> toAbstract (OldName x)
        args <- toAbstract ps
        return $ A.LHSHead x args
    toAbstract (C.LHSProj d ps1 l ps2) = do
        qx <- resolveName d
        d  <- case qx of
                FieldName d -> return $ anameName d
                UnknownName -> notInScope d
                _           -> typeError $ GenericError $
                  "head of copattern needs to be a field identifier, but "
                  ++ show d ++ " isn't one"
        args1 <- toAbstract ps1
        l     <- toAbstract l
        args2 <- toAbstract ps2
        return $ A.LHSProj d args1 l args2

instance ToAbstract c a => ToAbstract (Arg c) (Arg a) where
    toAbstract (Arg h r e) = Arg h r <$> toAbstractCtx (hiddenArgumentCtx h) e

instance ToAbstract c a => ToAbstract (Named name c) (Named name a) where
    toAbstract (Named n e) = Named n <$> toAbstract e

{- DOES NOT WORK ANYMORE with pattern synonyms
instance ToAbstract c a => ToAbstract (A.LHSCore' c) (A.LHSCore' a) where
    toAbstract = mapM toAbstract
-}

instance ToAbstract (A.LHSCore' C.Expr) (A.LHSCore' A.Expr) where
    toAbstract (A.LHSHead f ps)             = A.LHSHead f <$> mapM toAbstract ps
    toAbstract (A.LHSProj d ps lhscore ps') = A.LHSProj d <$> mapM toAbstract ps
      <*> mapM toAbstract lhscore <*> mapM toAbstract ps'

-- Patterns are done in two phases. First everything but the dot patterns, and
-- then the dot patterns. This is because dot patterns can refer to variables
-- bound anywhere in the pattern.

instance ToAbstract (A.Pattern' C.Expr) (A.Pattern' A.Expr) where
    toAbstract (A.VarP x)             = return $ A.VarP x
    toAbstract (A.ConP i ds as)       = A.ConP i ds <$> mapM toAbstract as
    toAbstract (A.DefP i x as)        = A.DefP i x <$> mapM toAbstract as
    toAbstract (A.WildP i)            = return $ A.WildP i
    toAbstract (A.AsP i x p)          = A.AsP i x <$> toAbstract p
    toAbstract (A.DotP i e)           = A.DotP i <$> toAbstract e
    toAbstract (A.AbsurdP i)          = return $ A.AbsurdP i
    toAbstract (A.LitP l)             = return $ A.LitP l
    toAbstract (A.ImplicitP i)        = return $ A.ImplicitP i
    toAbstract (A.PatternSynP i x as) = do
        p   <- lookupPatternSyn x
        as' <- mapM toAbstract as
        instPatternSyn p as'
      where
        instPatternSyn :: A.PatternSynDefn -> [NamedArg A.Pattern] -> ScopeM A.Pattern
        instPatternSyn (ns, p) as
            | length ns == length as = return $ substPattern s $ setRange (getRange i) p
            | otherwise              = typeError $ PatternSynonymArityMismatch x
          where
          s = zipWith' (\n a -> (n, namedThing (unArg a))) ns as


instance ToAbstract C.Pattern (A.Pattern' C.Expr) where

    toAbstract p@(C.IdentP x) = do
        px <- toAbstract (PatName x)
        case px of
            VarPatName y        -> return $ VarP y
            ConPatName ds       -> return $ ConP (PatRange (getRange p))
                                                 (AmbQ $ map anameName ds)
                                                 []
            PatternSynPatName d -> return $ PatternSynP (PatRange (getRange p))
                                                        (anameName d) []

    toAbstract p0@(AppP p q) = do
        (p', q') <- toAbstract (p,q)
        case p' of
            ConP _ x as        -> return $ ConP info x (as ++ [q'])
            DefP _ x as        -> return $ DefP info x (as ++ [q'])
            PatternSynP _ x as -> return $ PatternSynP info x (as ++ [q'])
            _                  -> typeError $ InvalidPattern p0
        where
            r = getRange p0
            info = PatSource r $ \pr -> if appBrackets pr then ParenP r p0 else p0

    toAbstract p0@(OpAppP r op ps) = do
        p <- toAbstract (IdentP op)
        ps <- toAbstract ps
        case p of
          ConP        _ x as -> return $ ConP info x
                                    (as ++ map (Arg NotHidden Relevant . unnamed) ps)
          DefP        _ x as -> return $ DefP info x
                                    (as ++ map (Arg NotHidden Relevant . unnamed) ps)
          PatternSynP _ x as -> return $ PatternSynP info x
                                    (as ++ map (Arg NotHidden Relevant . unnamed) ps)
          _                  -> __IMPOSSIBLE__
        where
            r    = getRange p0
            info = PatSource r $ \pr -> if appBrackets pr then ParenP r p0 else p0

    -- Removed when parsing
    toAbstract (HiddenP _ _)   = __IMPOSSIBLE__
    toAbstract (InstanceP _ _) = __IMPOSSIBLE__
    toAbstract (RawAppP _ _)   = __IMPOSSIBLE__

    toAbstract p@(C.WildP r)    = return $ A.WildP (PatSource r $ const p)
    toAbstract (C.ParenP _ p)   = toAbstract p
    toAbstract (C.LitP l)       = return $ A.LitP l
    toAbstract p0@(C.AsP r x p) = typeError $ NotSupported "@-patterns"
      {- do
        x <- toAbstract (NewName x)
        p <- toAbstract p
        return $ A.AsP info x p
        where
            info = PatSource r $ \_ -> p0
      -}
    -- we have to do dot patterns at the end
    toAbstract p0@(C.DotP r e) = return $ A.DotP info e
        where info = PatSource r $ \_ -> p0
    toAbstract p0@(C.AbsurdP r) = return $ A.AbsurdP info
        where info = PatSource r $ \_ -> p0

-- | Turn an operator application into abstract syntax. Make sure to record the
-- right precedences for the various arguments.
toAbstractOpApp :: C.QName -> [OpApp C.Expr] -> ScopeM A.Expr
toAbstractOpApp op es = do
    f  <- getFixity op
    let (_,_,parts) = oldToNewNotation $ (op, f)
    op <- toAbstract (OldQName op)
    foldl' app op <$> left (theFixity f) [p | p <- parts, not (isBindingHole p)] es
    where
        app e arg = A.App (ExprRange (fuseRange e arg)) e
                  $ Arg NotHidden Relevant $ unnamed arg

        left f (IdPart _ : xs) es = inside f xs es
        left f (_ : xs) (e : es) = do
            e  <- toAbstractOpArg (LeftOperandCtx f) e
            es <- inside f xs es
            return (e : es)
        left f (_  : _)  [] = __IMPOSSIBLE__
        left f []        _  = __IMPOSSIBLE__

        inside f [x]          es       = right f x es
        inside f (IdPart _ : xs) es       = inside f xs es
        inside f (_  : xs) (e : es) = do
            e  <- toAbstractOpArg InsideOperandCtx e
            es <- inside f xs es
            return (e : es)
        inside _ (_ : _) [] = __IMPOSSIBLE__
        inside _ []         _  = __IMPOSSIBLE__

        right _ (IdPart _)  [] = return []
        right f _          [e] = do
            e <- toAbstractOpArg (RightOperandCtx f) e
            return [e]
        right _ _     _  = __IMPOSSIBLE__
