{-# LANGUAGE CPP, MultiParamTypeClasses, FlexibleInstances,
             UndecidableInstances
  #-}

module Agda.Interaction.BasicOps where
{- TODO: The operations in this module should return Expr and not String,
         for this we need to write a translator from Internal to Abstract syntax.
-}


import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State
import qualified Data.Map as Map
import Data.Map (Map)
import Data.List
import Data.Maybe

import Agda.Interaction.Monad

import qualified Agda.Syntax.Concrete as C -- ToDo: Remove with instance of ToConcrete
import Agda.Syntax.Position
import Agda.Syntax.Abstract as A hiding (Open)
import Agda.Syntax.Common
import Agda.Syntax.Info(ExprInfo(..),MetaInfo(..))
import Agda.Syntax.Internal as I
import Agda.Syntax.Translation.InternalToAbstract
import Agda.Syntax.Translation.AbstractToConcrete
import Agda.Syntax.Translation.ConcreteToAbstract
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad
import Agda.Syntax.Fixity(Precedence(..))
import Agda.Syntax.Parser

import Agda.TypeChecker
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Monad as M
import Agda.TypeChecking.MetaVars
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.EtaContract (etaContract)
import Agda.TypeChecking.Coverage
import Agda.TypeChecking.Records
import Agda.TypeChecking.Pretty (prettyTCM)
import qualified Agda.TypeChecking.Pretty as TP

import Agda.Utils.Monad
import Agda.Utils.Pretty
import Agda.Utils.Permutation
import Agda.Utils.Size

#include "../undefined.h"
import Agda.Utils.Impossible

-- | Parses an expression.

parseExpr :: Range -> String -> TCM C.Expr
parseExpr rng s = liftIO $ parsePosString exprParser pos s
  where
  pos = case rStart rng of
          Just pos -> pos
          Nothing  -> startPos Nothing

parseExprIn :: InteractionId -> Range -> String -> TCM Expr
parseExprIn ii rng s = do
    mId <- lookupInteractionId ii
    updateMetaVarRange mId rng
    mi  <- getMetaInfo <$> lookupMeta mId
    e   <- parseExpr rng s
    concreteToAbstract (clScope mi) e

giveExpr :: MetaId -> Expr -> TCM Expr
-- When translater from internal to abstract is given, this function might return
-- the expression returned by the type checker.
giveExpr mi e =
    do  mv <- lookupMeta mi
        withMetaInfo (getMetaInfo mv) $ metaTypeCheck' mi e mv

  where  metaTypeCheck' mi e mv =
            case mvJudgement mv of
		 HasType _ t  -> do
		    ctx <- getContextArgs
		    let t' = t `piApply` ctx
		    v	<- checkExpr e t'
		    case mvInstantiation mv of
			InstV v' ->
			  addConstraints =<< equalTerm t' v (v' `apply` ctx)
			_	 -> updateMeta mi v
		    reify v
		 IsSort _ -> __IMPOSSIBLE__

give :: InteractionId -> Maybe Range -> Expr -> TCM (Expr,[InteractionId])
give ii mr e = liftTCM $ do
  mi <- lookupInteractionId ii
  mis <- getInteractionPoints
  r <- getInteractionRange ii
  updateMetaVarRange mi $ maybe r id mr
  giveExpr mi e `catchError` \err -> case errError err of
    PatternErr _ -> do
      err <- withInteractionId ii $ TP.text "Failed to give" TP.<+> prettyTCM e
      typeError $ GenericError $ show err
    _ -> throwError err
  removeInteractionPoint ii
  mis' <- getInteractionPoints
  return (e, mis' \\ mis)


addDecl :: Declaration -> TCM ([InteractionId])
addDecl d = do
  mis <- getInteractionPoints
  checkDecl d
  mis' <- getInteractionPoints
  return (mis' \\ mis)


refine :: InteractionId -> Maybe Range -> Expr -> TCM (Expr,[InteractionId])
-- If constants has a fixed arity, then it might be better to do
-- exact refinement.
refine ii mr e =
    do  mi <- lookupInteractionId ii
        mv <- lookupMeta mi
        let range = maybe (getRange mv) id mr
        let scope = M.getMetaScope mv
        tryRefine 10 range scope e
  where tryRefine :: Int -> Range -> ScopeInfo -> Expr -> TCM (Expr,[InteractionId])
        tryRefine nrOfMetas r scope e = try nrOfMetas e
           where try 0 e = throwError (strMsg "Can not refine")
                 try n e = give ii (Just r) e `catchError` (\_ -> try (n-1) (appMeta e))
                 appMeta :: Expr -> Expr
                 appMeta e =
                      let metaVar = QuestionMark
				  $ Agda.Syntax.Info.MetaInfo
				    { Agda.Syntax.Info.metaRange = r
                                    , Agda.Syntax.Info.metaScope = scope { scopePrecedence = ArgumentCtx }
				    , metaNumber = Nothing
				    }
                      in App (ExprRange $ r) e (Arg NotHidden $ unnamed metaVar)
                 --ToDo: The position of metaVar is not correct
                 --ToDo: The fixity of metavars is not correct -- fixed? MT

{-
refineExact :: InteractionId -> Maybe Range -> Expr -> TCM (Expr,[InteractionId])
refineExact ii mr e =
    do  mi <- lookupInteractionId ii
        mv <- lookupMeta mi
        let range = maybe (getRange mv) id mr
        let scope = M.getMetaScope mv
        (_,t) <- withMetaInfo (getMetaInfo mv) $ inferExpr e
        let arityt = arity t

        tryRefine 10 range scope e
  where tryRefine :: Int -> Range -> ScopeInfo -> Expr -> TCM (Expr,[InteractionId])
        tryRefine nrOfMetas r scope e = try nrOfMetas e
           where try 0 e = throwError (strMsg "Can not refine")
                 try n e = give ii (Just r) e `catchError` (\_ -> try (n-1) (appMeta e))
                 appMeta :: Expr -> Expr
                 appMeta e =
                      let metaVar = QuestionMark $ Agda.Syntax.Info.MetaInfo {Agda.Syntax.Info.metaRange = r,
                                                 Agda.Syntax.Info.metaScope = scope}
                      in App (ExprRange $ r) NotHidden e metaVar
                 --ToDo: The position of metaVar is not correct





abstract :: InteractionId -> Maybe Range -> TCM (Expr,[InteractionId])
abstract ii mr


refineExact :: InteractionId -> Expr -> TCM (Expr,[InteractionId])
refineExact ii e =
    do
-}


{-| Evaluate the given expression in the current environment -}
evalInCurrent :: Expr -> TCM Expr
evalInCurrent e =
    do  t <- newTypeMeta_
	v <- checkExpr e t
	v' <- etaContract =<< normalise v
	reify v'


evalInMeta :: InteractionId -> Expr -> TCM Expr
evalInMeta ii e =
   do 	m <- lookupInteractionId ii
	mi <- getMetaInfo <$> lookupMeta m
	withMetaInfo mi $
	    evalInCurrent e


data Rewrite =  AsIs | Instantiated | HeadNormal | Normalised

--rewrite :: Rewrite -> Term -> TCM Term
rewrite AsIs	     t = return t
rewrite Instantiated t = return t   -- reify does instantiation
rewrite HeadNormal   t = etaContract =<< reduce t
rewrite Normalised   t = etaContract =<< normalise t


data OutputForm a b
      = OfType b a | CmpInType Comparison a b b
                   | CmpTerms [Polarity] a [b] [b]
      | JustType b | CmpTypes Comparison b b
                   | CmpTeles Comparison b b
      | JustSort b | CmpSorts Comparison b b
      | Guard (OutputForm a b) [OutputForm a b]
      | Assign b a | TypedAssign b a a
      | IsEmptyType a

-- | A subset of 'OutputForm'.

data OutputForm' a b = OfType' { ofName :: b
                               , ofExpr :: a
                               }

outputFormId :: OutputForm a b -> b
outputFormId o = case o of
  OfType i _           -> i
  CmpInType _ _ i _    -> i
  CmpTerms _ _ (i:_) _ -> i
  CmpTerms _ _ [] _    -> __IMPOSSIBLE__
  JustType i           -> i
  CmpTypes _ i _       -> i
  CmpTeles _ i _       -> i
  JustSort i           -> i
  CmpSorts _ i _       -> i
  Guard o _            -> outputFormId o
  Assign i _           -> i
  TypedAssign i _ _    -> i
  IsEmptyType _        -> __IMPOSSIBLE__   -- Should never be used on IsEmpty constraints

instance Functor (OutputForm a) where
    fmap f (OfType e t)           = OfType (f e) t
    fmap f (JustType e)           = JustType (f e)
    fmap f (JustSort e)           = JustSort (f e)
    fmap f (CmpInType cmp t e e') = CmpInType cmp t (f e) (f e')
    fmap f (CmpTerms cmp t e e')  = CmpTerms cmp t (map f e) (map f e')
    fmap f (CmpTypes cmp e e')    = CmpTypes cmp (f e) (f e')
    fmap f (CmpTeles cmp e e')    = CmpTeles cmp (f e) (f e')
    fmap f (CmpSorts cmp e e')    = CmpSorts cmp (f e) (f e')
    fmap f (Guard o os)           = Guard (fmap f o) (fmap (fmap f) os)
    fmap f (Assign m e)           = Assign (f m) e
    fmap f (TypedAssign m e a)    = TypedAssign (f m) e a
    fmap f (IsEmptyType a)        = IsEmptyType a

instance Reify Constraint (OutputForm Expr Expr) where
    reify (ValueCmp cmp t u v)   = CmpInType cmp <$> reify t <*> reify u <*> reify v
    reify (ArgsCmp cmp t u v)    = CmpTerms cmp <$> reify t
                                                <*> mapM (reify . unArg) u
                                                <*> mapM (reify . unArg) v
    reify (TypeCmp cmp t t')     = CmpTypes cmp <$> reify t <*> reify t'
    reify (TelCmp  cmp t t')     = CmpTeles cmp <$> (ETel <$> reify t) <*> (ETel <$> reify t')
    reify (SortCmp cmp s s')     = CmpSorts cmp <$> reify s <*> reify s'
    reify (Guarded c cs) = do
	o  <- reify c
	os <- mapM (withConstraint reify) cs
	return $ Guard o os
    reify (UnBlock m) = do
        mi <- mvInstantiation <$> lookupMeta m
        case mi of
          BlockedConst t -> do
            e  <- reify t
            m' <- reify (MetaV m [])
            return $ Assign m' e
          PostponedTypeCheckingProblem cl -> enterClosure cl $ \(e, a, _) -> do
            a  <- reify a
            m' <- reify (MetaV m [])
            return $ TypedAssign m' e a
          Open{}  -> __IMPOSSIBLE__
          InstS{} -> __IMPOSSIBLE__
          InstV{} -> __IMPOSSIBLE__
    reify (IsEmpty a) = IsEmptyType <$> reify a

showComparison :: Comparison -> String
showComparison CmpEq  = " = "
showComparison CmpLeq = " =< "

instance (Show a,Show b) => Show (OutputForm a b) where
    show (OfType e t)           = show e ++ " : " ++ show t
    show (JustType e)           = "Type " ++ show e
    show (JustSort e)           = "Sort " ++ show e
    show (CmpInType cmp t e e') = show e ++ showComparison cmp ++ show e' ++ " : " ++ show t
    show (CmpTerms cmp t e e')  = show e ++ "~~" ++ show e' ++ " : " ++ show t
    show (CmpTypes  cmp t t')   = show t ++ showComparison cmp ++ show t'
    show (CmpTeles  cmp t t')   = show t ++ showComparison cmp ++ show t'
    show (CmpSorts cmp s s')    = show s ++ showComparison cmp ++ show s'
    show (Guard o os)           = show o ++ "  if  " ++ show os
    show (Assign m e)           = show m ++ " := " ++ show e
    show (TypedAssign m e a)    = show m ++ " := " ++ show e ++ " : " ++ show a
    show (IsEmptyType a)        = "Is empty: " ++ show a

instance (ToConcrete a c, ToConcrete b d) =>
         ToConcrete (OutputForm a b) (OutputForm c d) where
    toConcrete (OfType e t) = OfType <$> toConcrete e <*> toConcrete t
    toConcrete (JustType e) = JustType <$> toConcrete e
    toConcrete (JustSort e) = JustSort <$> toConcrete e
    toConcrete (CmpInType cmp t e e') =
      CmpInType cmp <$> toConcrete t <*> toConcrete e <*> toConcrete e'
    toConcrete (CmpTerms cmp t e e') =
      CmpTerms cmp <$> toConcrete t <*> mapM toConcrete e <*> mapM toConcrete e'
    toConcrete (CmpTypes cmp e e') = CmpTypes cmp <$> toConcrete e <*> toConcrete e'
    toConcrete (CmpTeles cmp e e') = CmpTeles cmp <$> toConcrete e <*> toConcrete e'
    toConcrete (CmpSorts cmp e e') = CmpSorts cmp <$> toConcrete e <*> toConcrete e'
    toConcrete (Guard o os) = Guard <$> toConcrete o <*> toConcrete os
    toConcrete (Assign m e) = Assign <$> toConcrete m <*> toConcrete e
    toConcrete (TypedAssign m e a) = TypedAssign <$> toConcrete m <*> toConcrete e <*> toConcrete a
    toConcrete (IsEmptyType a) = IsEmptyType <$> toConcrete a

instance (Pretty a, Pretty b) => Pretty (OutputForm' a b) where
  pretty (OfType' e t) = pretty e <+> text ":" <+> pretty t

instance (ToConcrete a c, ToConcrete b d) =>
            ToConcrete (OutputForm' a b) (OutputForm' c d) where
  toConcrete (OfType' e t) = OfType' <$> toConcrete e <*> toConcrete t

--ToDo: Move somewhere else
instance ToConcrete InteractionId C.Expr where
    toConcrete (InteractionId i) = return $ C.QuestionMark noRange (Just i)
instance ToConcrete MetaId C.Expr where
    toConcrete (MetaId i) = return $ C.Underscore noRange (Just i)

judgToOutputForm :: Judgement a c -> OutputForm a c
judgToOutputForm (HasType e t) = OfType e t
judgToOutputForm (IsSort s)    = JustSort s

--- Printing Operations
getConstraint :: Int -> TCM (OutputForm Expr Expr)
getConstraint ci =
    do  cc <- lookupConstraint ci
        cc <- reduce cc
        withConstraint reify cc


getConstraints :: TCM [OutputForm C.Expr C.Expr]
getConstraints = liftTCM $ do
    cs <- mapM (withConstraint (abstractToConcrete_ <.> reify)) =<< reduce =<< M.getConstraints
    ss <- mapM toOutputForm =<< getSolvedInteractionPoints
    return $ ss ++ cs
  where
    toOutputForm (ii, mi, e) = do
      mv <- getMetaInfo <$> lookupMeta mi
      withMetaInfo mv $ do
        let m = QuestionMark $ MetaInfo noRange emptyScopeInfo (Just $ fromIntegral ii)
        abstractToConcrete_ $ Assign m e

getSolvedInteractionPoints :: TCM [(InteractionId, MetaId, Expr)]
getSolvedInteractionPoints = do
  is <- getInteractionPoints
  concat <$> mapM solution is
  where
    solution i = do
      m  <- lookupInteractionId i
      mv <- lookupMeta m
      withMetaInfo (getMetaInfo mv) $ do
        args  <- getContextArgs
        scope <- getScope
        let sol v = do e <- reify v; return [(i, m, ScopedExpr scope e)]
            unsol = return []
        case mvInstantiation mv of
          InstV{}                        -> sol (MetaV m args)
          InstS{}                        -> sol (Sort $ MetaS m args)
          Open{}                         -> unsol
          BlockedConst{}                 -> unsol
          PostponedTypeCheckingProblem{} -> unsol

typeOfMetaMI :: Rewrite -> MetaId -> TCM (OutputForm Expr MetaId)
typeOfMetaMI norm mi =
     do mv <- lookupMeta mi
	withMetaInfo (getMetaInfo mv) $
	  rewriteJudg mv (mvJudgement mv)
   where
    rewriteJudg mv (HasType i t) = do
      t <- rewrite norm t
      vs <- getContextArgs
      reportSDoc "interactive.meta" 10 $ TP.vcat
        [ TP.text $ unwords ["permuting", show i, "with", show $ mvPermutation mv]
        , TP.nest 2 $ TP.vcat
          [ TP.text "len  =" TP.<+> TP.text (show $ length vs)
          , TP.text "args =" TP.<+> prettyTCM vs
          , TP.text "t    =" TP.<+> prettyTCM t
          ]
        ]
      OfType i <$> reify (t `piApply` permute (takeP (size vs) $ mvPermutation mv) vs)
    rewriteJudg mv (IsSort i)    = return $ JustSort i


typeOfMeta :: Rewrite -> InteractionId -> TCM (OutputForm Expr InteractionId)
typeOfMeta norm ii =
     do mi <- lookupInteractionId ii
        out <- typeOfMetaMI norm mi
        return $ fmap (\_ -> ii) out

typesOfVisibleMetas :: Rewrite -> TCM [OutputForm Expr InteractionId]
typesOfVisibleMetas norm =
  liftTCM $ mapM (typeOfMeta norm) =<< getInteractionPoints

typesOfHiddenMetas :: Rewrite -> TCM [OutputForm Expr MetaId]
typesOfHiddenMetas norm = liftTCM $ do
  is    <- getInteractionMetas
  store <- Map.filterWithKey (openAndImplicit is) <$> getMetaStore
  mapM (typeOfMetaMI norm) $ Map.keys store
  where
  openAndImplicit is x (MetaVar{mvInstantiation = M.Open}) = x `notElem` is
  openAndImplicit is x (MetaVar{mvInstantiation = M.BlockedConst _}) = True
  openAndImplicit _  _ _                                    = False

-- Gives a list of names and corresponding types.

contextOfMeta :: InteractionId -> Rewrite -> TCM [OutputForm' Expr Name]
contextOfMeta ii norm = do
  info <- getMetaInfo <$> (lookupMeta =<< lookupInteractionId ii)
  let localVars = map ctxEntry . envContext . clEnv $ info
  withMetaInfo info $ gfilter visible <$> reifyContext localVars
  where gfilter p = catMaybes . map p
        visible (OfType x y) | show x /= "_" = Just (OfType' x y)
                             | otherwise     = Nothing
	visible _	     = __IMPOSSIBLE__
        reifyContext xs = reverse <$> zipWithM out [1..] xs

        out i (Arg h (x, t)) = escapeContext i $ do
          t' <- reify =<< rewrite norm t
          return $ OfType x t'


{-| Returns the type of the expression in the current environment -}
typeInCurrent :: Rewrite -> Expr -> TCM Expr
typeInCurrent norm e =
    do 	(_,t) <- inferExpr e
        v <- rewrite norm t
        reify v



typeInMeta :: InteractionId -> Rewrite -> Expr -> TCM Expr
typeInMeta ii norm e =
   do 	m <- lookupInteractionId ii
	mi <- getMetaInfo <$> lookupMeta m
	withMetaInfo mi $
	    typeInCurrent norm e

withInteractionId :: InteractionId -> TCM a -> TCM a
withInteractionId i ret = do
  m <- lookupInteractionId i
  withMetaId m ret

withMetaId :: MetaId -> TCM a -> TCM a
withMetaId m ret = do
  info <- lookupMeta m
  withMetaInfo (mvInfo info) ret

-- The intro tactic

-- Returns the terms (as strings) that can be
-- used to refine the goal. Uses the coverage checker
-- to find out which constructors are possible.
introTactic :: InteractionId -> TCM [String]
introTactic ii = do
  mi <- lookupInteractionId ii
  mv <- lookupMeta mi
  withMetaInfo (getMetaInfo mv) $ case mvJudgement mv of
    HasType _ t -> do
        t <- reduce =<< piApply t <$> getContextArgs
        case unEl t of
          I.Def d _ -> do
            def <- getConstInfo d
            case theDef def of
              Datatype{}                 -> introData t
              Record{ recNamedCon = name }
                | name      -> introData t
                | otherwise -> introRec d
              _                          -> return []
          _ -> do
            TelV tel _ <- telView t
            case tel of
              EmptyTel -> return []
              tel      -> introFun tel
     `catchError` \_ -> return []
    _ -> __IMPOSSIBLE__
  where
    conName [Arg _ (I.ConP c _)] = [c]
    conName [_]                = []
    conName _                  = __IMPOSSIBLE__

    showTCM v = show <$> prettyTCM v

    introFun tel = addCtxTel tel' $ do
        imp <- showImplicitArguments
        let okHiding h = imp || h == NotHidden
        vars <- mapM showTCM [ Arg h (I.Var i [])
                             | (h, i) <- zip hs $ reverse [0..n - 1]
                             , okHiding h
                             ]
        return [ unwords $ ["λ"] ++ vars ++ ["→", "?"] ]
      where
        n = size tel
        hs   = map argHiding $ telToList tel
        tel' = telFromList [ fmap makeName b | b <- telToList tel ]
        makeName ("_", t) = ("x", t)
        makeName (x, t)   = (x, t)

    introData t = do
      let tel  = telFromList [Arg NotHidden ("_", t)]
          perm = idP 1
          pat  = [Arg NotHidden (I.VarP "c")]
      r <- split tel perm pat 0
      case r of
        Left err -> return []
        Right cs -> mapM showTCM $ concatMap (conName . scPats) cs

    introRec d = do
      hfs <- getRecordFieldNames d
      fs <- ifM showImplicitArguments
            (return $ map snd hfs)
            (return [ f | (NotHidden, f) <- hfs ])
      return
        [ concat $
            "record {" :
            intersperse ";" (map (\ f -> show f ++ " = ?") fs) ++
            ["}"]
        ]

-- | Runs the given computation as if in an anonymous goal at the end
-- of the top-level module.

atTopLevel :: TCM a -> TCM a
atTopLevel m = do
  mCurrent <- stCurrentModule <$> get
  case mCurrent of
    Nothing      -> typeError $
                      GenericError "The file has not been loaded yet."
    Just current -> do
      r <- getVisitedModule (toTopLevelModuleName current)
      case r of
        Nothing -> __IMPOSSIBLE__
        Just mi -> do
          tel <- lookupSection current
          M.withCurrentModule current $
            withScope_ (iInsideScope $ miInterface mi) $
              addCtxTel tel $
                m

-- | Returns the contents of the given module.

moduleContents :: Range
                  -- ^ The range of the next argument.
               -> String
                  -- ^ The module name.
               -> TCM ([C.Name], [(C.Name, Type)])
                  -- ^ Module names, names paired up with
                  -- corresponding types.
moduleContents rng s = do
  m <- parseExpr rng s
  m <- case m of
         C.Ident m              -> return m
         C.RawApp _ [C.Ident m] -> return m
         _                      -> typeError $
           GenericError $ "Not a module name: " ++ show m ++ "."
  modScope <- getNamedScope . amodName =<< resolveModule m
  let modules :: ThingsInScope AbstractModule
      modules = exportedNamesInScope modScope
      names :: ThingsInScope AbstractName
      names = exportedNamesInScope modScope
  types <- mapM (\(x, n) -> do
                   d <- getConstInfo $ anameName n
                   t <- defType <$> instantiateDef d
                   return (x, t))
                (concatMap (\(x, ns) -> map ((,) x) ns) $
                           Map.toList names)
  return (Map.keys modules, types)
