{-# LANGUAGE CPP, MultiParamTypeClasses, FlexibleInstances,
             UndecidableInstances, DeriveFunctor
  #-}

module Agda.Interaction.BasicOps where

import Control.Applicative
import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State
import qualified Data.Map as Map
import Data.Map (Map)
import Data.List
import Data.Maybe

import qualified Agda.Syntax.Concrete as C -- ToDo: Remove with instance of ToConcrete
import Agda.Syntax.Position
import Agda.Syntax.Abstract as A hiding (Open)
import Agda.Syntax.Common
import Agda.Syntax.Info(ExprInfo(..),MetaInfo(..),emptyMetaInfo)
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
import Agda.TypeChecking.Monad as M hiding (MetaInfo)
import Agda.TypeChecking.MetaVars
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.EtaContract (etaContract)
import Agda.TypeChecking.Coverage
import Agda.TypeChecking.Records
import Agda.TypeChecking.Irrelevance (wakeIrrelevantVars)
import Agda.TypeChecking.Pretty (prettyTCM)
-- UNUSED: import Agda.TypeChecking.Eliminators (unElim)
import qualified Agda.TypeChecking.Pretty as TP

import Agda.Utils.List
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
-- When translator from internal to abstract is given, this function might return
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
			InstV v' -> whenM ((Irrelevant /=) <$> asks envRelevance) $
                                      equalTerm t' v (v' `apply` ctx)
			_	 -> updateMeta mi v
		    reify v
		 IsSort{} -> __IMPOSSIBLE__

give :: InteractionId -> Maybe Range -> Expr -> TCM (Expr,[InteractionId])
give ii mr e = liftTCM $ do
  mi <- lookupInteractionId ii
  mis <- getInteractionPoints
  r <- getInteractionRange ii
  updateMetaVarRange mi $ maybe r id mr
  giveExpr mi e `catchError` \err -> case err of
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
                                    , metaNameSuggestion = ""
				    }
                      in App (ExprRange $ r) e (defaultArg $ unnamed metaVar)
                 --ToDo: The position of metaVar is not correct
                 --ToDo: The fixity of metavars is not correct -- fixed? MT

{-| Evaluate the given expression in the current environment -}
evalInCurrent :: Expr -> TCM Expr
evalInCurrent e =
    do  (v, t) <- inferExpr e
	v' <- {- etaContract =<< -} normalise v
	reify v'


evalInMeta :: InteractionId -> Expr -> TCM Expr
evalInMeta ii e =
   do 	m <- lookupInteractionId ii
	mi <- getMetaInfo <$> lookupMeta m
	withMetaInfo mi $
	    evalInCurrent e


data Rewrite =  AsIs | Instantiated | HeadNormal | Normalised
    deriving (Read)

--rewrite :: Rewrite -> Term -> TCM Term
rewrite AsIs	     t = return t
rewrite Instantiated t = return t   -- reify does instantiation
rewrite HeadNormal   t = {- etaContract =<< -} reduce t
rewrite Normalised   t = {- etaContract =<< -} normalise t


data OutputForm a b = OutputForm ProblemId (OutputConstraint a b)
  deriving (Functor)

data OutputConstraint a b
      = OfType b a | CmpInType Comparison a b b
                   | CmpElim [Polarity] a [b] [b]
      | JustType b | CmpTypes Comparison b b
                   | CmpLevels Comparison b b
                   | CmpTeles Comparison b b
      | JustSort b | CmpSorts Comparison b b
      | Guard (OutputConstraint a b) ProblemId
      | Assign b a | TypedAssign b a a
      | IsEmptyType a | FindInScopeOF b a [(a,a)]
  deriving (Functor)

-- | A subset of 'OutputConstraint'.

data OutputConstraint' a b = OfType' { ofName :: b
                                     , ofExpr :: a
                                     }

outputFormId :: OutputForm a b -> b
outputFormId (OutputForm _ o) = out o
  where
    out o = case o of
      OfType i _           -> i
      CmpInType _ _ i _    -> i
      CmpElim _ _ (i:_) _  -> i
      CmpElim _ _ [] _     -> __IMPOSSIBLE__
      JustType i           -> i
      CmpLevels _ i _      -> i
      CmpTypes _ i _       -> i
      CmpTeles _ i _       -> i
      JustSort i           -> i
      CmpSorts _ i _       -> i
      Guard o _            -> out o
      Assign i _           -> i
      TypedAssign i _ _    -> i
      IsEmptyType _        -> __IMPOSSIBLE__   -- Should never be used on IsEmpty constraints
      FindInScopeOF _ _ _  -> __IMPOSSIBLE__

instance Reify ProblemConstraint (Closure (OutputForm Expr Expr)) where
  reify (PConstr pid cl) = enterClosure cl $ \c -> buildClosure =<< (OutputForm pid <$> reify c)

instance Reify Constraint (OutputConstraint Expr Expr) where
    reify (ValueCmp cmp t u v)   = CmpInType cmp <$> reify t <*> reify u <*> reify v
    reify (ElimCmp cmp t v es1 es2) =
      CmpElim cmp <$> reify t <*> reify es1
                              <*> reify es2
    reify (LevelCmp cmp t t')    = CmpLevels cmp <$> reify t <*> reify t'
    reify (TypeCmp cmp t t')     = CmpTypes cmp <$> reify t <*> reify t'
    reify (TelCmp a b cmp t t')  = CmpTeles cmp <$> (ETel <$> reify t) <*> (ETel <$> reify t')
    reify (SortCmp cmp s s')     = CmpSorts cmp <$> reify s <*> reify s'
    reify (Guarded c pid) = do
	o  <- reify c
	return $ Guard o pid
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
          OpenIFS{}  -> __IMPOSSIBLE__
          InstS{} -> __IMPOSSIBLE__
          InstV{} -> __IMPOSSIBLE__
    reify (FindInScope m cands) = do
      m' <- reify (MetaV m [])
      ctxArgs <- getContextArgs
      t <- getMetaType m
      t' <- reify t
      cands' <- mapM (\(tm,ty) -> (,) <$> reify tm <*> reify ty) cands
      return $ FindInScopeOF m' t' cands' -- IFSTODO
    reify (IsEmpty r a) = IsEmptyType <$> reify a

showComparison :: Comparison -> String
showComparison CmpEq  = " = "
showComparison CmpLeq = " =< "

instance (Show a,Show b) => Show (OutputForm a b) where
  show (OutputForm 0   c) = show c
  show (OutputForm pid c) = "[" ++ show pid ++ "] " ++ show c

instance (Show a,Show b) => Show (OutputConstraint a b) where
    show (OfType e t)           = show e ++ " : " ++ show t
    show (JustType e)           = "Type " ++ show e
    show (JustSort e)           = "Sort " ++ show e
    show (CmpInType cmp t e e') = show e ++ showComparison cmp ++ show e' ++ " : " ++ show t
    show (CmpElim cmp t e e')   = show e ++ " == " ++ show e' ++ " : " ++ show t
    show (CmpTypes  cmp t t')   = show t ++ showComparison cmp ++ show t'
    show (CmpLevels cmp t t')   = show t ++ showComparison cmp ++ show t'
    show (CmpTeles  cmp t t')   = show t ++ showComparison cmp ++ show t'
    show (CmpSorts cmp s s')    = show s ++ showComparison cmp ++ show s'
    show (Guard o pid)          = show o ++ " [blocked by problem " ++ show pid ++ "]"
    show (Assign m e)           = show m ++ " := " ++ show e
    show (TypedAssign m e a)    = show m ++ " := " ++ show e ++ " :? " ++ show a
    show (IsEmptyType a)        = "Is empty: " ++ show a
    show (FindInScopeOF s t cs) = "Resolve implicit argument " ++ showCand (s,t) ++ ". Candidates: [" ++
                                    intercalate ", " (map showCand cs) ++ "]"
      where showCand (tm,ty) = show tm ++ " : " ++ show ty

instance (ToConcrete a c, ToConcrete b d) =>
         ToConcrete (OutputForm a b) (OutputForm c d) where
    toConcrete (OutputForm pid c) = OutputForm pid <$> toConcrete c

instance (ToConcrete a c, ToConcrete b d) =>
         ToConcrete (OutputConstraint a b) (OutputConstraint c d) where
    toConcrete (OfType e t) = OfType <$> toConcrete e <*> toConcreteCtx TopCtx t
    toConcrete (JustType e) = JustType <$> toConcrete e
    toConcrete (JustSort e) = JustSort <$> toConcrete e
    toConcrete (CmpInType cmp t e e') =
      CmpInType cmp <$> toConcreteCtx TopCtx t <*> toConcreteCtx ArgumentCtx e
                                               <*> toConcreteCtx ArgumentCtx e'
    toConcrete (CmpElim cmp t e e') =
      CmpElim cmp <$> toConcreteCtx TopCtx t <*> toConcreteCtx TopCtx e <*> toConcreteCtx TopCtx e'
    toConcrete (CmpTypes cmp e e') = CmpTypes cmp <$> toConcreteCtx ArgumentCtx e
                                                  <*> toConcreteCtx ArgumentCtx e'
    toConcrete (CmpLevels cmp e e') = CmpLevels cmp <$> toConcreteCtx ArgumentCtx e
                                                    <*> toConcreteCtx ArgumentCtx e'
    toConcrete (CmpTeles cmp e e') = CmpTeles cmp <$> toConcrete e <*> toConcrete e'
    toConcrete (CmpSorts cmp e e') = CmpSorts cmp <$> toConcreteCtx ArgumentCtx e
                                                  <*> toConcreteCtx ArgumentCtx e'
    toConcrete (Guard o pid) = Guard <$> toConcrete o <*> pure pid
    toConcrete (Assign m e) = noTakenNames $ Assign <$> toConcrete m <*> toConcreteCtx TopCtx e
    toConcrete (TypedAssign m e a) = TypedAssign <$> toConcrete m <*> toConcreteCtx TopCtx e
                                                                  <*> toConcreteCtx TopCtx a
    toConcrete (IsEmptyType a) = IsEmptyType <$> toConcreteCtx TopCtx a
    toConcrete (FindInScopeOF s t cs) =
      FindInScopeOF <$> toConcrete s <*> toConcrete t
                    <*> mapM (\(tm,ty) -> (,) <$> toConcrete tm <*> toConcrete ty) cs

instance (Pretty a, Pretty b) => Pretty (OutputConstraint' a b) where
  pretty (OfType' e t) = pretty e <+> text ":" <+> pretty t

instance (ToConcrete a c, ToConcrete b d) =>
            ToConcrete (OutputConstraint' a b) (OutputConstraint' c d) where
  toConcrete (OfType' e t) = OfType' <$> toConcrete e <*> toConcreteCtx TopCtx t

--ToDo: Move somewhere else
instance ToConcrete InteractionId C.Expr where
    toConcrete (InteractionId i) = return $ C.QuestionMark noRange (Just i)
{- UNUSED
instance ToConcrete MetaId C.Expr where
    toConcrete x@(MetaId i) = do
      return $ C.Underscore noRange (Just $ "_" ++ show i)
-}
instance ToConcrete NamedMeta C.Expr where
    toConcrete i = do
      return $ C.Underscore noRange (Just $ show i)

judgToOutputForm :: Judgement a c -> OutputConstraint a c
judgToOutputForm (HasType e t) = OfType e t
judgToOutputForm (IsSort  s t) = JustSort s

getConstraints :: TCM [OutputForm C.Expr C.Expr]
getConstraints = liftTCM $ do
    cs <- M.getAllConstraints
    cs <- forM cs $ \c -> do
            cl <- reify c
            enterClosure cl abstractToConcrete_
    ss <- mapM toOutputForm =<< getSolvedInteractionPoints
    return $ ss ++ cs
  where
    toOutputForm (ii, mi, e) = do
      mv <- getMetaInfo <$> lookupMeta mi
      withMetaInfo mv $ do
        let m = QuestionMark $ emptyMetaInfo { metaNumber = Just $ fromIntegral ii }
        abstractToConcrete_ $ OutputForm 0 $ Assign m e

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
          InstS{}                        -> sol (Level $ Max [Plus 0 $ MetaLevel m args])
          Open{}                         -> unsol
          OpenIFS{}                         -> unsol
          BlockedConst{}                 -> unsol
          PostponedTypeCheckingProblem{} -> unsol

typeOfMetaMI :: Rewrite -> MetaId -> TCM (OutputConstraint Expr NamedMeta)
typeOfMetaMI norm mi =
     do mv <- lookupMeta mi
	withMetaInfo (getMetaInfo mv) $
	  rewriteJudg mv (mvJudgement mv)
   where
    rewriteJudg mv (HasType i t) = do
      ms <- getMetaNameSuggestion i
      t <- rewrite norm t
      vs <- getContextArgs
      let x = NamedMeta ms i
      reportSDoc "interactive.meta" 10 $ TP.vcat
        [ TP.text $ unwords ["permuting", show i, "with", show $ mvPermutation mv]
        , TP.nest 2 $ TP.vcat
          [ TP.text "len  =" TP.<+> TP.text (show $ length vs)
          , TP.text "args =" TP.<+> prettyTCM vs
          , TP.text "t    =" TP.<+> prettyTCM t
          , TP.text "x    =" TP.<+> TP.text (show x)
          ]
        ]
      OfType x <$> reify (t `piApply` permute (takeP (size vs) $ mvPermutation mv) vs)
    rewriteJudg mv (IsSort i t) = do
      ms <- getMetaNameSuggestion i
      return $ JustSort $ NamedMeta ms i


typeOfMeta :: Rewrite -> InteractionId -> TCM (OutputConstraint Expr InteractionId)
typeOfMeta norm ii =
     do mi <- lookupInteractionId ii
        out <- typeOfMetaMI norm mi
        return $ fmap (\_ -> ii) out

typesOfVisibleMetas :: Rewrite -> TCM [OutputConstraint Expr InteractionId]
typesOfVisibleMetas norm =
  liftTCM $ mapM (typeOfMeta norm) =<< getInteractionPoints

typesOfHiddenMetas :: Rewrite -> TCM [OutputConstraint Expr NamedMeta]
typesOfHiddenMetas norm = liftTCM $ do
  is    <- getInteractionMetas
  store <- Map.filterWithKey (openAndImplicit is) <$> getMetaStore
  mapM (typeOfMetaMI norm) $ Map.keys store
  where
  openAndImplicit is x (MetaVar{mvInstantiation = M.Open}) = x `notElem` is
  openAndImplicit is x (MetaVar{mvInstantiation = M.BlockedConst _}) = True
  openAndImplicit _  _ _                                    = False

-- Gives a list of names and corresponding types.

contextOfMeta :: InteractionId -> Rewrite -> TCM [OutputConstraint' Expr Name]
contextOfMeta ii norm = do
  info <- getMetaInfo <$> (lookupMeta =<< lookupInteractionId ii)
  let localVars = map ctxEntry . envContext . clEnv $ info
  withMetaInfo info $ gfilter visible <$> reifyContext localVars
  where gfilter p = catMaybes . map p
        visible (OfType x y) | show x /= "_" = Just (OfType' x y)
                             | otherwise     = Nothing
	visible _	     = __IMPOSSIBLE__
        reifyContext xs = reverse <$> zipWithM out [1..] xs

        out i (Dom h _ (x, t)) = escapeContext i $ do
          t' <- reify =<< rewrite norm t
          return $ OfType x t'


-- | Returns the type of the expression in the current environment
--   We wake up irrelevant variables just in case the user want to
--   invoke that command in an irrelevant context.
typeInCurrent :: Rewrite -> Expr -> TCM Expr
typeInCurrent norm e =
    do 	(_,t) <- wakeIrrelevantVars $ inferExpr e
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
  mv <- lookupMeta m
  withMetaInfo' mv ret

-- The intro tactic

-- Returns the terms (as strings) that can be
-- used to refine the goal. Uses the coverage checker
-- to find out which constructors are possible.
introTactic :: Bool -> InteractionId -> TCM [String]
introTactic pmLambda ii = do
  mi <- lookupInteractionId ii
  mv <- lookupMeta mi
  withMetaInfo (getMetaInfo mv) $ case mvJudgement mv of
    HasType _ t -> do
        t <- reduce =<< piApply t <$> getContextArgs
        case ignoreSharing $ unEl t of
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
    conName [Arg _ _ (I.ConP c _ _)] = [c]
    conName [_]                      = []
    conName _                        = __IMPOSSIBLE__

    showTCM v = show <$> prettyTCM v

    introFun tel = addCtxTel tel' $ do
        imp <- showImplicitArguments
        let okHiding0 h = imp || h == NotHidden
            -- if none of the vars were displayed, we would get a parse error
            -- thus, we switch to displaying all
            allHidden   = null (filter okHiding0 hs)
            okHiding    = if allHidden then const True else okHiding0
        vars <- -- setShowImplicitArguments (imp || allHidden) $
                (if allHidden then withShowAllArguments else id) $
                  mapM showTCM [ Arg h Relevant (var i)
                               | (h, i) <- zip hs $ downFrom n
                               , okHiding h
                               ]
        if pmLambda
           then return [ unwords $ ["λ", "{"] ++ vars ++ ["→", "?", "}"] ]
           else return [ unwords $ ["λ"]      ++ vars ++ ["→", "?"] ]
      where
        n = size tel
        hs   = map domHiding $ telToList tel
        tel' = telFromList [ fmap makeName b | b <- telToList tel ]
        makeName ("_", t) = ("x", t)
        makeName (x, t)   = (x, t)

    introData t = do
      let tel  = telFromList [domFromArg $ defaultArg ("_", t)]
          pat  = [defaultArg (I.VarP "c")]
      r <- splitLast CoInductive tel pat
      case r of
        Left err -> return []
        Right cov -> mapM showTCM $ concatMap (conName . scPats) $ splitClauses cov

    introRec d = do
      hfs <- getRecordFieldNames d
      fs <- ifM showImplicitArguments
            (return $ map unArg hfs)
            (return [ f | (Arg NotHidden _ f) <- hfs ])
      return
        [ concat $
            "record {" :
            intersperse ";" (map (\ f -> show f ++ " = ?") fs) ++
            ["}"]
        ]

-- | Runs the given computation as if in an anonymous goal at the end
-- of the top-level module.

atTopLevel :: TCM a -> TCM a
atTopLevel m = inConcreteMode $ do
  mCurrent <- stCurrentModule <$> get
  case mCurrent of
    Nothing      -> typeError $
                      GenericError "The file has not been loaded yet."
    Just current -> do
      r <- getVisitedModule (toTopLevelModuleName current)
      case r of
        Nothing -> __IMPOSSIBLE__
        Just mi -> do
          let scope = iInsideScope $ miInterface mi
          tel <- lookupSection current
          M.withCurrentModule current $
            withScope_ scope $
              addContext (zipWith' (fmap . (,))
                                   (reverse $ map snd $ scopeLocals scope)
                                   (map (fmap snd) $ telToList tel)) $
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
