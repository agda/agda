{-# LANGUAGE CPP, MultiParamTypeClasses, FunctionalDependencies,
             FlexibleInstances, UndecidableInstances, OverlappingInstances
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
import Data.Traversable (mapM)
import Data.List ((\\), nub)
import qualified Data.Map as Map

import Agda.Syntax.Concrete as C hiding (topLevelModuleName)
import Agda.Syntax.Abstract as A
import Agda.Syntax.Position
import Agda.Syntax.Common
import Agda.Syntax.Info
import Agda.Syntax.Concrete.Definitions as C
import Agda.Syntax.Concrete.Operators
import Agda.Syntax.Fixity
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad
import Agda.Syntax.Strict

import Agda.TypeChecking.Monad.Base (TypeError(..), Call(..), typeError,
                                     TCErr(..), TCErr'(..))
import Agda.TypeChecking.Monad.Trace (traceCall, traceCallCPS, setCurrentRange)
import Agda.TypeChecking.Monad.State
import Agda.TypeChecking.Monad.Options

import {-# SOURCE #-} Agda.Interaction.Imports (scopeCheckImport)

import Agda.Utils.Monad
import Agda.Utils.Tuple
import Agda.Utils.List
import Agda.Utils.Fresh

#include "../../undefined.h"
import Agda.Utils.Impossible


{--------------------------------------------------------------------------
    Exceptions
 --------------------------------------------------------------------------}

notAModuleExpr e            = typeError $ NotAModuleExpr e
notAnExpression e           = typeError $ NotAnExpression e
notAValidLetBinding d       = typeError $ NotAValidLetBinding d
nothingAppliedToHiddenArg e = typeError $ NothingAppliedToHiddenArg e

-- Debugging

printLocals :: Int -> String -> ScopeM ()
printLocals v s = verboseS "scope.top" v $ do
  locals <- scopeLocals <$> getScope
  reportSLn "" 0 $ s ++ " " ++ show locals

printScope :: String -> Int -> String -> ScopeM ()
printScope tag v s = verboseS ("scope." ++ tag) v $ do
  scope <- getScope
  reportSLn "" 0 $ s ++ " " ++ show scope

{--------------------------------------------------------------------------
    Helpers
 --------------------------------------------------------------------------}

lhsArgs :: C.Pattern -> (C.Name, [NamedArg C.Pattern])
lhsArgs p = case appView p of
    Arg _ (Named _ (IdentP (C.QName x))) : ps -> (x, ps)
    _                                         -> __IMPOSSIBLE__
    where
        mkHead    = Arg NotHidden . unnamed
        notHidden = Arg NotHidden . unnamed
        appView p = case p of
            AppP p arg    -> appView p ++ [arg]
            OpAppP _ x ps -> mkHead (IdentP $ C.QName x) : map notHidden ps
            ParenP _ p    -> appView p
            RawAppP _ _   -> __IMPOSSIBLE__
            _             -> [ mkHead p ]

annotateDecl :: ScopeM A.Declaration -> ScopeM A.Declaration
annotateDecl m = annotateDecls $ (:[]) <$> m

annotateDecls :: ScopeM [A.Declaration] -> ScopeM A.Declaration
annotateDecls m = do
  ds <- m
  s  <- getScope
  return $ ScopedDecl s ds

annotateDefn :: ScopeM A.Definition -> ScopeM A.Definition
annotateDefn m = do
  d <- m
  s <- getScope
  return $ ScopedDef s d

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
      A.VarP x        -> [nameConcrete x]
      A.ConP _ _ args -> concatMap (vars . namedThing . unArg) args
      A.WildP _       -> []
      A.AsP _ x p     -> nameConcrete x : vars p
      A.DotP _ _      -> []
      A.AbsurdP _     -> []
      A.LitP _        -> []
      A.DefP _ _ args -> __IMPOSSIBLE__
      A.ImplicitP _   -> __IMPOSSIBLE__

-- | Compute the type of the record constructor (with bogus target type)
recordConstructorType :: [NiceDeclaration] -> C.Expr
recordConstructorType fields = build fs
  where
    fs = reverse $ dropWhile notField $ reverse fields

    notField NiceField{} = False
    notField _           = True

    build (NiceField r f _ _ x e : fs) = C.Pi [C.TypedBindings r NotHidden
                                                [C.TBind r [BName x f] e]
                                              ] $ build fs
      where r = getRange x
    build (d : fs)                     = C.Let noRange (notSoNiceDeclarations [d]) $ build fs
    build []                           = C.Prop noRange

checkModuleMacro apply r p x tel m args open dir = withLocalVars $ do
    notPublicWithoutOpen open dir

    tel' <- toAbstract tel
    (m0,m1,args') <- toAbstract ( NewModuleName x
                                , OldModuleName m
                                , args
                                )
    printScope "mod.inst" 20 "module macro"

    -- If we're opening, the import directive is applied to the open,
    -- otherwise to the module itself.
    let dir' = case open of
                DontOpen  -> dir
                DoOpen    -> defaultImportDir

    (renD, renM) <- withCurrentModule m0 $ do
      s  <- getNamedScope m1
      (s', renM, renD) <- copyScope m0 =<< getNamedScope m1
      s' <- applyImportDirectiveM (C.QName x) dir' s'
      modifyCurrentScope $ const s'
      printScope "mod.inst" 20 "copied source module"
      return (renD, renM)
    bindModule p x m0
    printScope "mod.inst" 20 "after copying"
    case open of
      DoOpen   -> openModule_ (C.QName x) dir
      DontOpen -> return ()
    printScope "mod.inst" 20 $ show open
    stripNoNames
    printScope "mod.inst" 10 $ "after stripping"
    return [ apply info (m0 `withRangesOf` [x]) tel' m1 args' renD renM ]
  where
    info = ModuleInfo
             { minfoRange  = r
             , minfoAsName = Nothing
             , minfoAsTo   = renamingRange dir
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
    mk DefName = Def
    mk ConName = Con . AmbQ . (:[])

instance ToAbstract OldQName A.Expr where
  toAbstract (OldQName x) = do
    qx <- resolveName x
    reportSLn "scope.name" 10 $ "resolved " ++ show x ++ ": " ++ show qx
    case qx of
      VarName x'         -> return $ A.Var x'
      DefinedName d      -> return $ nameExpr d
      ConstructorName ds -> return $ A.Con $ AmbQ (map anameName ds)
      UnknownName        -> notInScope x

data APatName = VarPatName A.Name
              | ConPatName [AbstractName]

instance ToAbstract PatName APatName where
  toAbstract (PatName x) = do
    reportSLn "scope.pat" 10 $ "checking pattern name: " ++ show x
    rx <- resolveName x
    z  <- case (rx, x) of
      -- TODO: warn about shadowing
      (VarName y,     C.QName x)                          -> return $ Left x -- typeError $ RepeatedVariableInPattern y x
      (DefinedName d, C.QName x) | DefName == anameKind d -> return $ Left x
      (UnknownName,   C.QName x)                          -> return $ Left x
      (ConstructorName ds, _)                             -> return $ Right ds
      _                                                   ->
        typeError $ GenericError $
          "Cannot pattern match on " ++ show x ++ ", because it is not a constructor"
    case z of
      Left x  -> do
        reportSLn "scope.pat" 10 $ "it was a var: " ++ show x
        p <- VarPatName <$> toAbstract (NewName x)
        printLocals 10 "bound it:"
        return p
      Right cs -> do
        reportSLn "scope.pat" 10 $ "it was a con: " ++ show (map anameName cs)
        return $ ConPatName cs

-- Should be a defined name.
instance ToAbstract OldName A.QName where
  toAbstract (OldName x) = do
    rx <- resolveName (C.QName x)
    case rx of
      DefinedName d -> return $ anameName d
      _             -> __IMPOSSIBLE__

newtype NewModuleName      = NewModuleName      C.Name
newtype NewModuleQName     = NewModuleQName     C.QName
newtype OldModuleName      = OldModuleName      C.QName

freshQModule :: A.ModuleName -> C.Name -> ScopeM A.ModuleName
freshQModule m x = A.qualifyM m . mnameFromList . (:[]) <$> freshAbstractName_ x

instance ToAbstract NewModuleName A.ModuleName where
  toAbstract (NewModuleName x) = do
    ms <- scopeLookup (C.QName x) <$> getScope
    unless (null ms) $ 
      typeError $ ShadowedModule $
                  map ((`withRangeOf` x) . amodName) ms
    m <- getCurrentModule
    y <- freshQModule m x
    createModule y
    return y

instance ToAbstract NewModuleQName A.ModuleName where
  toAbstract (NewModuleQName m) = toAbs noModuleName m
    where
      toAbs m (C.QName x)  = do
        y <- freshQModule m x
        createModule y
        return y
      toAbs m (C.Qual x q) = do
        m' <- freshQModule m x
        toAbs m' q

instance ToAbstract OldModuleName A.ModuleName where
  toAbstract (OldModuleName q) = amodName <$> resolveModule q

-- Expressions ------------------------------------------------------------

-- | Peel off 'C.HiddenArg' and represent it as an 'NamedArg'.
mkNamedArg :: C.Expr -> NamedArg C.Expr
mkNamedArg (C.HiddenArg _ e) = Arg Hidden e
mkNamedArg e                 = Arg NotHidden $ unnamed e

-- | Peel off 'C.HiddenArg' and represent it as an 'Arg', throwing away any name.
mkArg :: C.Expr -> Arg C.Expr
mkArg (C.HiddenArg _ e) = Arg Hidden $ namedThing e
mkArg e                 = Arg NotHidden e

instance ToAbstract C.Expr A.Expr where
  toAbstract e =
    traceCall (ScopeCheckExpr e) $ annotateExpr $ case e of
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
                    }
      C.Underscore r n -> do
        scope <- getScope
        return $ A.Underscore $ MetaInfo
                    { metaRange  = r
                    , metaScope  = scope
                    , metaNumber = n
                    }

  -- Raw application
      C.RawApp r es -> do
        e <- parseApplication es
        toAbstract e

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

  -- Lambda
      C.AbsurdLam r h -> return $ A.AbsurdLam (ExprRange r) h

      e0@(C.Lam r bs e) -> do
        localToAbstract bs $ \(b:bs') -> do
        e        <- toAbstractCtx TopCtx e
        let info = ExprRange r
        return $ A.Lam info b $ foldr mkLam e bs'
        where
            mkLam b e = A.Lam (ExprRange $ fuseRange b e) b e

  -- Function types
      C.Fun r e1 e2 -> do
        e1 <- toAbstractCtx FunctionSpaceDomainCtx $ mkArg e1
        e2 <- toAbstractCtx TopCtx e2
        let info = ExprRange r
        return $ A.Fun info e1 e2

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

  -- Parenthesis
      C.Paren _ e -> toAbstractCtx TopCtx e

  -- Pattern things
      C.As _ _ _ -> notAnExpression e
      C.Dot _ _  -> notAnExpression e
      C.Absurd _ -> notAnExpression e

  -- Impossible things
      C.ETel _   -> __IMPOSSIBLE__

instance ToAbstract C.LamBinding A.LamBinding where
  toAbstract (C.DomainFree h x) = A.DomainFree h <$> toAbstract (NewName x)
  toAbstract (C.DomainFull tb)  = A.DomainFull <$> toAbstract tb

instance ToAbstract C.TypedBindings A.TypedBindings where
  toAbstract (C.TypedBindings r h bs) = A.TypedBindings r h <$> toAbstract bs

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
    ds <- withLocalVars $ do
            tel <- toAbstract tel
            (:[]) . A.Section info (qm `withRangesOfQ` x) tel <$>
              toAbstract ds
    scope <- getScope
    return (scope, ds)

  -- Binding is done by the caller
  printScope "module" 20 $ "after module " ++ show x
  return res
  where
    info = ModuleInfo r noRange Nothing

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


niceDecls :: [C.Declaration] -> ScopeM [NiceDeclaration]
niceDecls ds = case runNice $ niceDeclarations ds of
  Left e   -> throwError $ TCErr Nothing $ Exception (getRange e) (show e)
  Right ds -> return ds

instance ToAbstract [C.Declaration] [A.Declaration] where
  toAbstract ds = toAbstract =<< niceDecls ds

newtype LetDefs = LetDefs [C.Declaration]
newtype LetDef = LetDef NiceDeclaration

instance ToAbstract LetDefs [A.LetBinding] where
    toAbstract (LetDefs ds) =
        concat <$> (toAbstract =<< map LetDef <$> niceDecls ds)

instance ToAbstract LetDef [A.LetBinding] where
    toAbstract (LetDef d) =
        case d of
            NiceDef _ c [C.Axiom _ _ _ _ x t] [C.FunDef _ _ _ _ _ _ [cl]] ->
                do  e <- letToAbstract cl
                    t <- toAbstract t
                    x <- toAbstract (NewName x)
                    return [ A.LetBind (LetRange $ getRange c) x t e ]

            -- You can't open public in a let
            NiceOpen r x dirs | not (C.publicOpen dirs) -> do
              m       <- toAbstract (OldModuleName x)
              n       <- length . scopeLocals <$> getScope
              openModule_ x dirs
              return [A.LetOpen (ModuleInfo
                                   { minfoRange  = r
                                   , minfoAsName = Nothing
                                   , minfoAsTo   = renamingRange dirs
                                   })
                                m]

            NiceModuleMacro r p a x tel e open dir | not (C.publicOpen dir) -> case appView e of
              AppView (Ident m) args -> checkModuleMacro LetApply r p x tel m args open dir
              _                      -> notAModuleExpr e

            _   -> notAValidLetBinding d
        where
            letToAbstract (C.Clause top clhs@(C.LHS p [] [] []) (C.RHS rhs) NoWhere []) = do
                p    <- parseLHS (Just top) p
                localToAbstract (snd $ lhsArgs p) $ \args ->
                    do  rhs <- toAbstract rhs
                        foldM lambda rhs (reverse args)  -- just reverse because these DomainFree
            letToAbstract _ = notAValidLetBinding d

            -- Named patterns not allowed in let definitions
            lambda e (Arg h (Named Nothing (A.VarP x))) = return $ A.Lam i (A.DomainFree h x) e
                where
                    i = ExprRange (fuseRange x e)
            lambda e (Arg h (Named Nothing (A.WildP i))) =
                do  x <- freshNoName (getRange i)
                    return $ A.Lam i' (A.DomainFree h x) e
                where
                    i' = ExprRange (fuseRange i e)
            lambda _ _ = notAValidLetBinding d

instance ToAbstract C.Pragma [A.Pragma] where
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
            A.Con _ -> fail "Use HASKELL_DATA for constructors" -- TODO
            _       -> __IMPOSSIBLE__
      return [ A.CompiledPragma y hs ]
    toAbstract (C.BuiltinPragma _ b e) = do
        e <- toAbstract e
        return [ A.BuiltinPragma b e ]
    toAbstract (C.ImportPragma _ i) = do
      addHaskellImport i
      return []
    toAbstract (C.ImpossiblePragma _) = __IMPOSSIBLE__

-- Only constructor names are bound by definitions.
instance ToAbstract NiceDefinition Definition where

    toAbstract d = annotateDefn $ case d of

    -- Function definitions
      C.FunDef r ds f p a x cs ->
        traceCall (ScopeCheckDefinition d) $ do
          (x',cs') <- toAbstract (OldName x,cs)
          return $ A.FunDef (mkDefInfo x f p a r) x' cs'

    -- Data definitions
      C.DataDef r ind f p a x pars cons ->
        traceCall (ScopeCheckDefinition d) $
        withLocalVars $ do

          -- Check for duplicate constructors
          do let cs   = map conName cons
                 dups = nub $ cs \\ nub cs
                 bad  = filter (`elem` dups) cs
             unless (distinct cs) $
               setCurrentRange (getRange bad) $
                  typeError $ DuplicateConstructors dups

          pars <- toAbstract pars
          cons <- toAbstract (map Constr cons)
          x'   <- toAbstract (OldName x)
          printScope "data" 20 $ "Checked data " ++ show x
          return $ A.DataDef (mkDefInfo x f p a r) x' ind pars cons
        where
          conName (C.Axiom _ _ _ _ c _) = c
          conName _ = __IMPOSSIBLE__

    -- Record definitions (mucho interesting)
      C.RecDef r f p a x pars fields ->
        traceCall (ScopeCheckDefinition d) $
        withLocalVars $ do
          pars   <- toAbstract pars
          x'     <- toAbstract (OldName x)
          contel <- toAbstract $ recordConstructorType fields
          m0     <- getCurrentModule
          let m = A.qualifyM m0 $ mnameFromList $ (:[]) $ last $ qnameToList x'
          printScope "rec" 15 "before record"
          -- pushScope m
          createModule m
          afields <- withCurrentModule m $ do
            afields <- toAbstract fields
            printScope "rec" 15 "checked fields"
            return afields
            -- qm <- getCurrentModule
          -- popScope p
          bindModule p x m
          printScope "rec" 15 "record complete"
          return $ A.RecDef (mkDefInfo x f p a r) x' pars contel afields

-- The only reason why we return a list is that open declarations disappears.
-- For every other declaration we get a singleton list.
instance ToAbstract NiceDeclaration A.Declaration where

  toAbstract d = annotateDecls $
    traceCall (ScopeCheckDeclaration d) $
    case d of

  -- Axiom
    C.Axiom r f p a x t -> do
      t' <- toAbstractCtx TopCtx t
      y  <- freshAbstractQName f x
      bindName p DefName x y
      return [ A.Axiom (mkDefInfo x f p a r) y t' ]

  -- Fields
    C.NiceField r f p a x t -> do
      t' <- toAbstractCtx TopCtx t
      y  <- freshAbstractQName f x
      bindName p DefName x y
      return [ A.Field (mkDefInfo x f p a r) y t' ]

  -- Primitive function
    PrimitiveFunction r f p a x t -> do
      t' <- toAbstractCtx TopCtx t
      y  <- freshAbstractQName f x
      bindName p DefName x y
      return [ A.Primitive (mkDefInfo x f p a r) y t' ]

  -- Definitions (possibly mutual)
    NiceDef r cs ts ds -> do
      (ts', ds') <- toAbstract (ts, ds)
      return [ Definition (DeclInfo C.noName_ r) ts' ds' ]
                          -- TODO: what does the info mean here?

  -- TODO: what does an abstract module mean? The syntax doesn't allow it.
    NiceModule r p a (C.QName name) tel ds -> do
      aname <- toAbstract (NewModuleName name)
      x <- snd <$> scopeCheckModule r (C.QName name) aname tel ds
      bindModule p name aname
      return x

    NiceModule _ _ _ C.Qual{} _ _ -> __IMPOSSIBLE__

    NiceModuleMacro r p a x tel e open dir -> case appView e of
      AppView (Ident m) args -> checkModuleMacro Apply r p x tel m args open dir
      _                      -> notAModuleExpr e

    NiceOpen r x dir -> do
      m <- toAbstract (OldModuleName x)
      printScope "open" 20 $ "opening " ++ show x
      openModule_ x dir
      printScope "open" 20 $ "result:"
      return [A.Open (ModuleInfo
                        { minfoRange  = r
                        , minfoAsName = Nothing
                        , minfoAsTo   = renamingRange dir
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
                           })
                        m ]

instance ToAbstract (Constr C.NiceDeclaration) A.Declaration where
    toAbstract (Constr (C.Axiom r f p a x t)) = do
        t' <- toAbstractCtx TopCtx t
        y  <- freshAbstractQName f x
        bindName p' ConName x y
        return $ A.Axiom (mkDefInfo x f p a r) y t'
        where
            -- An abstract constructor is private (abstract constructor means
            -- abstract datatype, so the constructor should not be exported).
            p' = case (a, p) of
                    (AbstractDef, _) -> PrivateAccess
                    (_, p)           -> p

    toAbstract _ = __IMPOSSIBLE__    -- a constructor is always an axiom

instance ToAbstract C.Clause A.Clause where
    toAbstract (C.Clause top C.Ellipsis{} _ _ _) = fail "bad '...'" -- TODO: errors message
    toAbstract (C.Clause top lhs@(C.LHS p wps eqs with) rhs wh wcs) = withLocalVars $ do
      let wcs' = map (expandEllipsis p wps) wcs
      lhs' <- toAbstract (LeftHandSide top p wps)
      printLocals 10 "after lhs:"
      let (whname, whds) = case wh of
            NoWhere        -> (Nothing, [])
            AnyWhere ds    -> (Nothing, ds)
            SomeWhere m ds -> (Just m, ds)
      case whds of
        [] -> do
          rhs <- toAbstract =<< toAbstractCtx TopCtx (RightHandSide eqs with wcs' rhs)
          return $ A.Clause lhs' rhs []
        _       -> do
          m <- maybe (nameConcrete <$> freshNoName noRange) return whname
          let acc = maybe PrivateAccess (const PublicAccess) whname  -- unnamed where's are private
          let tel = []
          old <- getCurrentModule
          am  <- toAbstract (NewModuleName m)
          (scope, ds) <- scopeCheckModule (getRange wh) (C.QName m) am tel whds
          setScope scope
          -- the right hand side is checked inside the module of the local definitions
          rhs <- toAbstractCtx TopCtx (RightHandSide eqs with wcs' rhs)
          setCurrentModule old
--        case acc of
--          PublicAccess  -> popScope PublicAccess
--          PrivateAccess -> popScope_  -- unnamed where clauses are not in scope
          bindModule acc m am
          rhs <- toAbstract rhs
          return $ A.Clause lhs' rhs ds

data RightHandSide = RightHandSide [C.Expr] [C.Expr] [C.Clause] C.RHS
data AbstractRHS = AbsurdRHS'
                 | WithRHS' [A.Expr] [C.Clause]  -- ^ The with clauses haven't been translated yet
                 | RHS' A.Expr
                 | RewriteRHS' [A.Expr] AbstractRHS

instance ToAbstract AbstractRHS A.RHS where
  toAbstract AbsurdRHS'            = return A.AbsurdRHS
  toAbstract (RHS' e)              = return $ A.RHS e
  toAbstract (RewriteRHS' eqs rhs) = RewriteRHS eqs <$> toAbstract rhs
  toAbstract (WithRHS' es cs) = do
    m   <- getCurrentModule
    -- Hack
    NameId i _ <- fresh
    aux <- A.qualify m <$> freshName_ ("aux" ++ show i)
    A.WithRHS aux es <$> toAbstract cs

instance ToAbstract RightHandSide AbstractRHS where
  toAbstract (RightHandSide eqs@(_:_) es cs rhs) = do
    eqs <- toAbstractCtx TopCtx eqs
    rhs <- toAbstract (RightHandSide [] es cs rhs)
    return $ RewriteRHS' eqs rhs
  toAbstract (RightHandSide [] [] (_ : _) _)        = __IMPOSSIBLE__
  toAbstract (RightHandSide [] (_ : _) _ (C.RHS _)) = typeError $ BothWithAndRHS
  toAbstract (RightHandSide [] [] [] rhs)           = toAbstract rhs
  toAbstract (RightHandSide [] es cs C.AbsurdRHS)   = do
    es <- toAbstractCtx TopCtx es
    return $ WithRHS' es cs

instance ToAbstract C.RHS AbstractRHS where
    toAbstract C.AbsurdRHS = return $ AbsurdRHS'
    toAbstract (C.RHS e)   = RHS' <$> toAbstract e

data LeftHandSide = LeftHandSide C.Name C.Pattern [C.Pattern]

instance ToAbstract LeftHandSide A.LHS where
    toAbstract (LeftHandSide top lhs wps) =
      traceCall (ScopeCheckLHS top lhs) $ do
        p <- parseLHS (Just top) lhs
        printLocals 10 "before lhs:"
        let (x, ps) = lhsArgs p
        x    <- toAbstract (OldName x)
        args <- toAbstract ps
        wps  <- toAbstract =<< mapM (parseLHS Nothing) wps
        checkPatternLinearity (map (namedThing . unArg) args ++ wps)
        printLocals 10 "checked pattern:"
        args <- toAbstract args -- take care of dot patterns
        wps  <- toAbstract wps
        printLocals 10 "checked dots:"
        return $ A.LHS (LHSRange $ getRange (lhs, wps)) x args wps

instance ToAbstract c a => ToAbstract (Arg c) (Arg a) where
    toAbstract (Arg h e) = Arg h <$> toAbstractCtx (hiddenArgumentCtx h) e

instance ToAbstract c a => ToAbstract (Named name c) (Named name a) where
    toAbstract (Named n e) = Named n <$> toAbstract e

-- Patterns are done in two phases. First everything but the dot patterns, and
-- then the dot patterns. This is because dot patterns can refer to variables
-- bound anywhere in the pattern.

instance ToAbstract c a => ToAbstract (A.Pattern' c) (A.Pattern' a) where
    toAbstract = mapM toAbstract

instance ToAbstract C.Pattern (A.Pattern' C.Expr) where

    toAbstract p@(C.IdentP x) = do
        px <- toAbstract (PatName x)
        case px of
            VarPatName y  -> return $ VarP y
            ConPatName ds -> return $ ConP (PatRange (getRange p))
                                           (AmbQ $ map anameName ds)
                                           []

    toAbstract p0@(AppP p q) = do
        (p', q') <- toAbstract (p,q)
        case p' of
            ConP _ x as -> return $ ConP info x (as ++ [q'])
            DefP _ x as -> return $ DefP info x (as ++ [q'])
            _           -> typeError $ InvalidPattern p0
        where
            r = getRange p0
            info = PatSource r $ \pr -> if appBrackets pr then ParenP r p0 else p0

    toAbstract p0@(OpAppP r op ps) = do
        p <- toAbstract (IdentP $ C.QName op)
        ps <- toAbstract ps
        case p of
          ConP _ x as -> return $ ConP info x (as ++ map (Arg NotHidden . unnamed) ps)
          DefP _ x as -> return $ DefP info x (as ++ map (Arg NotHidden . unnamed) ps)
          _           -> __IMPOSSIBLE__
        where
            r = getRange p0
            info = PatSource r $ \pr -> if appBrackets pr then ParenP r p0 else p0

    -- Removed when parsing
    toAbstract (HiddenP _ _) = __IMPOSSIBLE__
    toAbstract (RawAppP _ _) = __IMPOSSIBLE__

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
        where
            info = PatSource r $ \_ -> p0

-- | Turn an operator application into abstract syntax. Make sure to record the
-- right precedences for the various arguments.
toAbstractOpApp :: C.Name -> [C.Expr] -> ScopeM A.Expr
toAbstractOpApp op@(C.NoName _ _) es = __IMPOSSIBLE__
toAbstractOpApp op@(C.Name _ xs) es = do
    f  <- getFixity (C.QName op)
    op <- toAbstract (OldQName $ C.QName op)
    foldl app op <$> left f xs es
    where
        app e arg = A.App (ExprRange (fuseRange e arg)) e
                  $ Arg NotHidden $ unnamed arg

        left f (Hole : xs) (e : es) = do
            e  <- toAbstractCtx (LeftOperandCtx f) e
            es <- inside f xs es
            return (e : es)
        left f (Id {} : xs) es = inside f xs es
        left f (Hole  : _)  [] = __IMPOSSIBLE__
        left f []           _  = __IMPOSSIBLE__

        inside f [x]          es       = right f x es
        inside f (Id {} : xs) es       = inside f xs es
        inside f (Hole  : xs) (e : es) = do
            e  <- toAbstractCtx InsideOperandCtx e
            es <- inside f xs es
            return (e : es)
        inside _ (Hole : _) [] = __IMPOSSIBLE__
        inside _ []         _  = __IMPOSSIBLE__

        right f Hole [e] = do
            e <- toAbstractCtx (RightOperandCtx f) e
            return [e]
        right _ (Id {})  [] = return []
        right _ Hole     _  = __IMPOSSIBLE__
        right _ (Id {})  _  = __IMPOSSIBLE__
