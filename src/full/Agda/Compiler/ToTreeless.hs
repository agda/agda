
module Agda.Compiler.ToTreeless
  ( toTreeless
  , closedTermToTreeless
  ) where

import Control.Arrow (first)
import Control.Monad.Reader

import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map

import Agda.Syntax.Common
import Agda.Syntax.Internal as I
import Agda.Syntax.Literal
import qualified Agda.Syntax.Treeless as C
import Agda.Syntax.Treeless (TTerm, EvaluationStrategy, ArgUsage(..))

import Agda.TypeChecking.CompiledClause as CC
import qualified Agda.TypeChecking.CompiledClause.Compile as CC
import Agda.TypeChecking.EtaContract (binAppView, BinAppView(..))
import Agda.TypeChecking.Monad as TCM
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Records (getRecordConstructor)
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute

import Agda.Compiler.Treeless.AsPatterns
import Agda.Compiler.Treeless.Builtin
import Agda.Compiler.Treeless.Erase
import Agda.Compiler.Treeless.Identity
import Agda.Compiler.Treeless.Simplify
import Agda.Compiler.Treeless.Uncase
import Agda.Compiler.Treeless.Unused

import Agda.Utils.Function
import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Pretty (prettyShow)
import qualified Agda.Utils.Pretty as P
import qualified Agda.Utils.SmallSet as SmallSet

import Agda.Utils.Impossible

prettyPure :: P.Pretty a => a -> TCM Doc
prettyPure = return . P.pretty

-- | Recompile clauses with forcing translation turned on.
getCompiledClauses :: QName -> TCM CC.CompiledClauses
getCompiledClauses q = do
  def <- getConstInfo q
  let cs = defClauses def
      isProj | Function{ funProjection = proj } <- theDef def = isJust (projProper =<< proj)
             | otherwise = False
      translate | isProj    = CC.DontRunRecordPatternTranslation
                | otherwise = CC.RunRecordPatternTranslation
  reportSDoc "treeless.convert" 40 $ "-- before clause compiler" $$ (pretty q <+> "=") <?> vcat (map pretty cs)
  let mst = funSplitTree $ theDef def
  reportSDoc "treeless.convert" 70 $
    caseMaybe mst "-- not using split tree" $ \st ->
      "-- using split tree" $$ pretty st
  CC.compileClauses' translate cs mst

-- | Converts compiled clauses to treeless syntax.
--
-- Note: Do not use any of the concrete names in the returned
-- term for identification purposes! If you wish to do so,
-- first apply the Agda.Compiler.Treeless.NormalizeNames
-- transformation.
toTreeless :: EvaluationStrategy -> QName -> TCM (Maybe C.TTerm)
toTreeless eval q = ifM (alwaysInline q) (pure Nothing) $ Just <$> toTreeless' eval q

toTreeless' :: EvaluationStrategy -> QName -> TCM C.TTerm
toTreeless' eval q =
  flip fromMaybeM (getTreeless q) $ verboseBracket "treeless.convert" 20 ("compiling " ++ prettyShow q) $ do
    cc <- getCompiledClauses q
    unlessM (alwaysInline q) $ setTreeless q (C.TDef q)
      -- so recursive inlining doesn't loop, but not for always inlined
      -- functions, since that would risk inlining to fail.
    ccToTreeless eval q cc

-- | Does not require the name to refer to a function.
cacheTreeless :: EvaluationStrategy -> QName -> TCM ()
cacheTreeless eval q = do
  def <- theDef <$> getConstInfo q
  case def of
    Function{} -> () <$ toTreeless' eval q
    _          -> return ()

ccToTreeless :: EvaluationStrategy -> QName -> CC.CompiledClauses -> TCM C.TTerm
ccToTreeless eval q cc = do
  let pbody b = pbody' "" b
      pbody' suf b = sep [ text (prettyShow q ++ suf) <+> "=", nest 2 $ prettyPure b ]
  v <- ifM (alwaysInline q) (return 20) (return 0)
  reportSDoc "treeless.convert" (30 + v) $ "-- compiled clauses of" <+> prettyTCM q $$ nest 2 (prettyPure cc)
  body <- casetreeTop eval cc
  reportSDoc "treeless.opt.converted" (30 + v) $ "-- converted" $$ pbody body
  body <- runPipeline eval q (compilerPipeline v q) body
  used <- usedArguments q body
  when (any (ArgUnused ==) used) $
    reportSDoc "treeless.opt.unused" (30 + v) $
      "-- used args:" <+> hsep [ if u == ArgUsed then text [x] else "_" | (x, u) <- zip ['a'..] used ] $$
      pbody' "[stripped]" (stripUnusedArguments used body)
  reportSDoc "treeless.opt.final" (20 + v) $ pbody body
  setTreeless q body
  setCompiledArgUse q used
  return body

data Pipeline = FixedPoint Int Pipeline
              | Sequential [Pipeline]
              | SinglePass CompilerPass

data CompilerPass = CompilerPass
  { passTag       :: String
  , passVerbosity :: Int
  , passName      :: String
  , passCode      :: EvaluationStrategy -> TTerm -> TCM TTerm
  }

compilerPass :: String -> Int -> String -> (EvaluationStrategy -> TTerm -> TCM TTerm) -> Pipeline
compilerPass tag v name code = SinglePass (CompilerPass tag v name code)

compilerPipeline :: Int -> QName -> Pipeline
compilerPipeline v q =
  Sequential
    -- Issue #4967: No simplification step before builtin translation! Simplification relies
    --              on either all or no builtins being translated. Since we might have inlined
    --              functions that have had the builtin translation applied, we need to apply it
    --              first.
    -- [ compilerPass "simpl"   (35 + v) "simplification"      $ const simplifyTTerm
    [ compilerPass "builtin" (30 + v) "builtin translation" $ const translateBuiltins
    , FixedPoint 5 $ Sequential
      [ compilerPass "simpl"  (30 + v) "simplification"     $ const simplifyTTerm
      , compilerPass "erase"  (30 + v) "erasure"            $ eraseTerms q
      , compilerPass "uncase" (30 + v) "uncase"             $ const caseToSeq
      , compilerPass "aspat"  (30 + v) "@-pattern recovery" $ const recoverAsPatterns
      ]
    , compilerPass "id" (30 + v) "identity function detection" $ const (detectIdentityFunctions q)
    ]

runPipeline :: EvaluationStrategy -> QName -> Pipeline -> TTerm -> TCM TTerm
runPipeline eval q pipeline t = case pipeline of
  SinglePass p   -> runCompilerPass eval q p t
  Sequential ps  -> foldM (flip $ runPipeline eval q) t ps
  FixedPoint n p -> runFixedPoint n eval q p t

runCompilerPass :: EvaluationStrategy -> QName -> CompilerPass -> TTerm -> TCM TTerm
runCompilerPass eval q p t = do
  t' <- passCode p eval t
  let dbg f   = reportSDoc ("treeless.opt." ++ passTag p) (passVerbosity p) $ f $ text ("-- " ++ passName p)
      pbody b = sep [ text (prettyShow q) <+> "=", nest 2 $ prettyPure b ]
  dbg $ if | t == t'   -> (<+> "(No effect)")
           | otherwise -> ($$ pbody t')
  return t'

runFixedPoint :: Int -> EvaluationStrategy -> QName -> Pipeline -> TTerm -> TCM TTerm
runFixedPoint n eval q pipeline = go 1
  where
    go i t | i > n = do
      reportSLn "treeless.opt.loop" 20 $ "++ Optimisation loop reached maximum iterations (" ++ show n ++ ")"
      return t
    go i t = do
      reportSLn "treeless.opt.loop" 30 $ "++ Optimisation loop iteration " ++ show i
      t' <- runPipeline eval q pipeline t
      if | t == t'   -> do
            reportSLn "treeless.opt.loop" 30 $ "++ Optimisation loop terminating after " ++ show i ++ " iterations"
            return t'
         | otherwise -> go (i + 1) t'

closedTermToTreeless :: EvaluationStrategy -> I.Term -> TCM C.TTerm
closedTermToTreeless eval t = do
  substTerm t `runReaderT` initCCEnv eval

alwaysInline :: QName -> TCM Bool
alwaysInline q = do
  def <- theDef <$> getConstInfo q
  pure $ case def of  -- always inline with functions and pattern lambdas
    Function{funClauses = cs} -> (isJust (funExtLam def) && not recursive) || isJust (funWith def)
            where
              recursive = any (fromMaybe True . clauseRecursive) cs
    _ -> False

-- | Initial environment for expression generation.
initCCEnv :: EvaluationStrategy -> CCEnv
initCCEnv eval = CCEnv
  { ccCxt        = []
  , ccCatchAll   = Nothing
  , ccEvaluation = eval
  }

-- | Environment for naming of local variables.
data CCEnv = CCEnv
  { ccCxt        :: CCContext  -- ^ Maps case tree de-bruijn indices to TTerm de-bruijn indices
  , ccCatchAll   :: Maybe Int  -- ^ TTerm de-bruijn index of the current catch all
  -- If an inner case has no catch-all clause, we use the one from its parent.
  , ccEvaluation :: EvaluationStrategy
  }

type CCContext = [Int]
type CC = ReaderT CCEnv TCM

shift :: Int -> CCContext -> CCContext
shift n = map (+n)

-- | Term variables are de Bruijn indices.
lookupIndex :: Int -- ^ Case tree de bruijn index.
    -> CCContext
    -> Int -- ^ TTerm de bruijn index.
lookupIndex i xs = fromMaybe __IMPOSSIBLE__ $ xs !!! i

-- | Case variables are de Bruijn levels.
lookupLevel :: Int -- ^ case tree de bruijn level
    -> CCContext
    -> Int -- ^ TTerm de bruijn index
lookupLevel l xs = fromMaybe __IMPOSSIBLE__ $ xs !!! (length xs - 1 - l)

-- | Compile a case tree into nested case and record expressions.
casetreeTop :: EvaluationStrategy -> CC.CompiledClauses -> TCM C.TTerm
casetreeTop eval cc = flip runReaderT (initCCEnv eval) $ do
  let a = commonArity cc
  lift $ reportSLn "treeless.convert.arity" 40 $ "-- common arity: " ++ show a
  lambdasUpTo a $ casetree cc

casetree :: CC.CompiledClauses -> CC C.TTerm
casetree cc = do
  case cc of
    CC.Fail -> return C.tUnreachable
    CC.Done xs v -> withContextSize (length xs) $ do
      -- Issue 2469: Body context size (`length xs`) may be smaller than current context size
      -- if some arguments are not used in the body.
      v <- lift (putAllowedReductions (SmallSet.fromList [ProjectionReductions, CopatternReductions]) $ normalise v)
      substTerm v
    CC.Case _ (CC.Branches True _ _ _ Just{} _ _) -> __IMPOSSIBLE__
      -- Andreas, 2016-06-03, issue #1986: Ulf: "no catch-all for copatterns!"
      -- lift $ do
      --   typeError . GenericDocError =<< do
      --     "Not yet implemented: compilation of copattern matching with catch-all clause"
    CC.Case (Arg _ n) (CC.Branches True conBrs _ _ Nothing _ _) -> lambdasUpTo n $ do
      mkRecord =<< traverse casetree (CC.content <$> conBrs)
    CC.Case (Arg _ n) (CC.Branches False conBrs etaBr litBrs catchAll _ lazy) -> lambdasUpTo (n + 1) $ do
                    -- We can treat eta-matches as regular matches here.
      let conBrs' = Map.union conBrs $ Map.fromList $ map (first conName) $ maybeToList etaBr
      if Map.null conBrs' && Map.null litBrs then do
        -- there are no branches, just return default
        updateCatchAll catchAll fromCatchAll
      else do
        let go p =
             case p of
              ((c:cs), []) -> do
                c' <- lift (canonicalName c)
                defn <- theDef <$> lift (getConstInfo c')
                case defn of
                  Constructor{conData = dtNm} -> return $ C.CTData dtNm
                  _                           -> go (cs , [])
              ([], (LitChar _):_)  -> return C.CTChar
              ([], (LitString _):_) -> return C.CTString
              ([], (LitFloat _):_) -> return C.CTFloat
              ([], (LitQName _):_) -> return C.CTQName
              _ -> __IMPOSSIBLE__

        caseTy <- go (Map.keys conBrs', Map.keys litBrs)
        updateCatchAll catchAll $ do
          x <- asks (lookupLevel n . ccCxt)
          def <- fromCatchAll
          let caseInfo = C.CaseInfo { caseType = caseTy, caseLazy = lazy }
          C.TCase x caseInfo def <$> do
            br1 <- conAlts n conBrs'
            br2 <- litAlts n litBrs
            return (br1 ++ br2)
  where
    -- normally, Agda should make sure that a pattern match is total,
    -- so we set the default to unreachable if no default has been provided.
    fromCatchAll :: CC C.TTerm
    fromCatchAll = asks (maybe C.tUnreachable C.TVar . ccCatchAll)

commonArity :: CC.CompiledClauses -> Int
commonArity cc =
  case arities 0 cc of
    [] -> 0
    as -> minimum as
  where
    arities cxt (Case (Arg _ x) (Branches False cons eta lits def _ _)) =
      concatMap (wArities cxt') (Map.elems cons) ++
      concatMap ((wArities cxt') . snd) (maybeToList eta) ++
      concatMap (wArities cxt' . WithArity 0) (Map.elems lits) ++
      concat [ arities cxt' c | Just c <- [def] ] -- ??
      where cxt' = max (x + 1) cxt
    arities cxt (Case _ Branches{projPatterns = True}) = [cxt]
    arities cxt (Done xs _) = [max cxt (length xs)]
    arities _   Fail        = []


    wArities cxt (WithArity k c) = map (\ x -> x - k + 1) $ arities (cxt - 1 + k) c

updateCatchAll :: Maybe CC.CompiledClauses -> (CC C.TTerm -> CC C.TTerm)
updateCatchAll Nothing cont = cont
updateCatchAll (Just cc) cont = do
  def <- casetree cc
  local (\e -> e { ccCatchAll = Just 0, ccCxt = shift 1 (ccCxt e) }) $ do
    C.mkLet def <$> cont

-- | Shrinks or grows the context to the given size.
-- Does not update the catchAll expression, the catchAll expression
-- MUST NOT be used inside `cont`.
withContextSize :: Int -> CC C.TTerm -> CC C.TTerm
withContextSize n cont = do
  diff <- asks (((n -) . length) . ccCxt)

  if diff <= 0
  then do
    let diff' = -diff
    local (\e -> e { ccCxt = shift diff . drop diff' $ ccCxt e }) $
      cont <&> (`C.mkTApp` map C.TVar (downFrom diff'))
  else do
    local (\e -> e { ccCxt = [0..(diff - 1)] ++ shift diff (ccCxt e)}) $ do
      createLambdas diff <$> do
        cont
  where createLambdas :: Int -> C.TTerm -> C.TTerm
        createLambdas 0 cont' = cont'
        createLambdas i cont' | i > 0 = C.TLam (createLambdas (i - 1) cont')
        createLambdas _ _ = __IMPOSSIBLE__

-- | Adds lambdas until the context has at least the given size.
-- Updates the catchAll expression to take the additional lambdas into account.
lambdasUpTo :: Int -> CC C.TTerm -> CC C.TTerm
lambdasUpTo n cont = do
  diff <- asks (((n -) . length) . ccCxt)

  if diff <= 0 then cont -- no new lambdas needed
  else do
    catchAll <- asks ccCatchAll

    withContextSize n $ do
      case catchAll of
        Just catchAll' -> do
          -- the catch all doesn't know about the additional lambdas, so just directly
          -- apply it again to the newly introduced lambda arguments.
          -- we also bind the catch all to a let, to avoid code duplication
          local (\e -> e { ccCatchAll = Just 0
                         , ccCxt = shift 1 (ccCxt e)}) $ do
            let catchAllArgs = map C.TVar $ downFrom diff
            C.mkLet (C.mkTApp (C.TVar $ catchAll' + diff) catchAllArgs)
              <$> cont
        Nothing -> cont

conAlts :: Int -> Map QName (CC.WithArity CC.CompiledClauses) -> CC [C.TAlt]
conAlts x br = forM (Map.toList br) $ \ (c, CC.WithArity n cc) -> do
  c' <- lift $ canonicalName c
  replaceVar x n $ do
    branch (C.TACon c' n) cc

litAlts :: Int -> Map Literal CC.CompiledClauses -> CC [C.TAlt]
litAlts x br = forM (Map.toList br) $ \ (l, cc) ->
  -- Issue1624: we need to drop the case scrutinee from the environment here!
  replaceVar x 0 $ do
    branch (C.TALit l ) cc

branch :: (C.TTerm -> C.TAlt) -> CC.CompiledClauses -> CC C.TAlt
branch alt cc = alt <$> casetree cc

-- | Replace de Bruijn Level @x@ by @n@ new variables.
replaceVar :: Int -> Int -> CC a -> CC a
replaceVar x n cont = do
  let upd cxt = shift n ys ++ ixs ++ shift n zs
       where
         -- compute the de Bruijn index
         i = length cxt - 1 - x
         -- discard index i
         (ys, _:zs) = splitAt i cxt
         -- compute the de-bruijn indexes of the newly inserted variables
         ixs = [0..(n - 1)]
  local (\e -> e { ccCxt = upd (ccCxt e) , ccCatchAll = (+n) <$> ccCatchAll e }) $
    cont


-- | Precondition: Map not empty.
mkRecord :: Map QName C.TTerm -> CC C.TTerm
mkRecord fs = lift $ do
  -- Get the name of the first field
  let p1 = fst $ headWithDefault __IMPOSSIBLE__ $ Map.toList fs
  -- Use the field name to get the record constructor and the field names.
  I.ConHead c IsRecord{} _ind xs <- conSrcCon . theDef <$> (getConstInfo =<< canonicalName . I.conName =<< recConFromProj p1)
  reportSDoc "treeless.convert.mkRecord" 60 $ vcat
    [ text "record constructor fields: xs      = " <+> (text . show) xs
    , text "to be filled with content: keys fs = " <+> (text . show) (Map.keys fs)
    ]
  -- Convert the constructor
  let (args :: [C.TTerm]) = for xs $ \ x -> Map.findWithDefault __IMPOSSIBLE__ (unArg x) fs
  return $ C.mkTApp (C.TCon c) args


recConFromProj :: QName -> TCM I.ConHead
recConFromProj q = do
  caseMaybeM (isProjection q) __IMPOSSIBLE__ $ \ proj -> do
    let d = unArg $ projFromType proj
    getRecordConstructor d


-- | Translate the actual Agda terms, with an environment of all the bound variables
--   from patternmatching. Agda terms are in de Bruijn indices, but the expected
--   TTerm de bruijn indexes may differ. This is due to additional let-bindings
--   introduced by the catch-all machinery, so we need to lookup casetree de bruijn
--   indices in the environment as well.
substTerm :: I.Term -> CC C.TTerm
substTerm term = normaliseStatic term >>= \ term ->
  case I.unSpine $ etaContractErased term of
    I.Var ind es -> do
      ind' <- asks (lookupIndex ind . ccCxt)
      let args = fromMaybe __IMPOSSIBLE__ $ I.allApplyElims es
      C.mkTApp (C.TVar ind') <$> substArgs args
    I.Lam _ ab ->
      C.TLam <$>
        local (\e -> e { ccCxt = 0 : shift 1 (ccCxt e) })
          (substTerm $ I.unAbs ab)
    I.Lit l -> return $ C.TLit l
    I.Level _ -> return C.TUnit
    I.Def q es -> do
      let args = fromMaybe __IMPOSSIBLE__ $ I.allApplyElims es
      maybeInlineDef q args
    I.Con c ci es -> do
        let args = fromMaybe __IMPOSSIBLE__ $ I.allApplyElims es
        c' <- lift $ canonicalName $ I.conName c
        C.mkTApp (C.TCon c') <$> substArgs args
    I.Pi _ _ -> return C.TUnit
    I.Sort _  -> return C.TSort
    I.MetaV x _ -> return $ C.TError $ C.TMeta $ prettyShow x
    I.DontCare _ -> return C.TErased
    I.Dummy{} -> __IMPOSSIBLE__

-- Andreas, 2019-07-10, issue #3792
-- | Eta-contract erased lambdas.
--
-- Should also be fine for strict backends:
--
--   * eta-contraction is semantics-preserving for total, effect-free languages.
--   * should a user rely on thunking, better not used an erased abstraction!
--
-- A live-or-death issue for the GHC 8.0 backend.  Consider:
-- @
--   foldl : ∀ {A} (B : Nat → Set)
--         → (f : ∀ {@0 n} → B n → A → B (suc n))
--         → (z : B 0)
--         → ∀ {@0 n} → Vec A n → B n
--   foldl B f z (x ∷ xs) = foldl (λ n → B (suc n)) (λ{@0 x} → f {suc x}) (f z x) xs
--   foldl B f z [] = z
-- @
-- The hidden composition of @f@ with @suc@, term @(λ{@0 x} → f {suc x})@,
-- can be eta-contracted to just @f@ by the compiler, since the first argument
-- of @f@ is erased.
--
-- GHC >= 8.2 seems to be able to do the optimization himself, but not 8.0.
--
etaContractErased :: I.Term -> I.Term
etaContractErased = trampoline etaErasedOnce
  where
  etaErasedOnce :: I.Term -> Either I.Term I.Term  -- Left = done, Right = jump again
  etaErasedOnce t =
    case t of

      -- If the abstraction is void, we don't have to strengthen.
      I.Lam _ (NoAbs _ v) ->
        case binAppView v of
          -- If the body is an application ending with an erased argument, eta-reduce!
          App u arg | not (usableModality arg) -> Right u
          _ -> done

      -- If the abstraction is non-void, only eta-contract if erased.
      I.Lam ai (Abs _ v) | not (usableModality ai) ->
        case binAppView v of
          -- If the body is an application ending with an erased argument, eta-reduce!
          -- We need to strengthen the function part then.
          App u arg | not (usableModality arg) -> Right $ subst 0 (DontCare __DUMMY_TERM__) u
          _ -> done

      _ -> done
    where
    done = Left t

normaliseStatic :: I.Term -> CC I.Term
normaliseStatic v@(I.Def f es) = lift $ do
  static <- isStaticFun . theDef <$> getConstInfo f
  if static then normalise v else pure v
normaliseStatic v = pure v

maybeInlineDef :: I.QName -> I.Args -> CC C.TTerm
maybeInlineDef q vs = do
  eval <- asks ccEvaluation
  ifM (lift $ alwaysInline q) (doinline eval) $ do
    lift $ cacheTreeless eval q
    def <- lift $ getConstInfo q
    case theDef def of
      fun@Function{}
        | fun ^. funInline -> doinline eval
        | otherwise -> do
        -- If ArgUsage hasn't been computed yet, we assume all arguments are used.
        used <- lift $ fromMaybe [] <$> getCompiledArgUse q
        let substUsed _   ArgUnused = pure C.TErased
            substUsed arg ArgUsed   = substArg arg
        C.mkTApp (C.TDef q) <$> zipWithM substUsed vs (used ++ repeat ArgUsed)
      _ -> C.mkTApp (C.TDef q) <$> substArgs vs
  where
    doinline eval = C.mkTApp <$> inline eval q <*> substArgs vs
    inline eval q = lift $ toTreeless' eval q

substArgs :: [Arg I.Term] -> CC [C.TTerm]
substArgs = traverse substArg

substArg :: Arg I.Term -> CC C.TTerm
substArg x | usableModality x = substTerm (unArg x)
           | otherwise = return C.TErased
