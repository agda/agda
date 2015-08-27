{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternGuards #-}

module Agda.TypeChecking.Monad.Signature where

import Prelude hiding (null)

import Control.Arrow (first, second, (***))
import Control.Applicative hiding (empty)
import Control.Monad.State
import Control.Monad.Reader

import Data.List hiding (null)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid

import Agda.Syntax.Abstract.Name
import Agda.Syntax.Abstract (Ren)
import Agda.Syntax.Common
import Agda.Syntax.Internal as I
import Agda.Syntax.Position

import qualified Agda.Compiler.JS.Parser as JS

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Context
import Agda.TypeChecking.Monad.Options
import Agda.TypeChecking.Monad.Env
import Agda.TypeChecking.Monad.Exception ( ExceptionT )
import Agda.TypeChecking.Monad.Mutual
import Agda.TypeChecking.Monad.Open
import Agda.TypeChecking.Monad.State
import Agda.TypeChecking.Positivity.Occurrence
import Agda.TypeChecking.Substitute
import {-# SOURCE #-} Agda.TypeChecking.CompiledClause.Compile
import {-# SOURCE #-} Agda.TypeChecking.Polarity
import {-# SOURCE #-} Agda.TypeChecking.ProjectionLike

import Agda.Utils.Except ( Error )
import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.Map as Map
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Permutation
import Agda.Utils.Pretty
import Agda.Utils.Size
import qualified Agda.Utils.HashMap as HMap

#include "undefined.h"
import Agda.Utils.Impossible

-- | Add a constant to the signature. Lifts the definition to top level.
addConstant :: QName -> Definition -> TCM ()
addConstant q d = do
  reportSLn "tc.signature" 20 $ "adding constant " ++ show q ++ " to signature"
  tel <- getContextTelescope
  let tel' = replaceEmptyName "r" $ killRange $ case theDef d of
              Constructor{} -> fmap (setHiding Hidden) tel
              _             -> tel
  let d' = abstract tel' $ d { defName = q }
  reportSLn "tc.signature" 30 $ "lambda-lifted definition = " ++ show d'
  modifySignature $ updateDefinitions $ HMap.insertWith (+++) q d'
  i <- currentOrFreshMutualBlock
  setMutualBlock i q
  where
    new +++ old = new { defDisplay = defDisplay new ++ defDisplay old
                      , defInstance = defInstance new `mplus` defInstance old }

-- | Set termination info of a defined function symbol.
setTerminates :: QName -> Bool -> TCM ()
setTerminates q b = modifySignature $ updateDefinition q $ updateTheDef $ setT
  where
    setT def@Function{} = def { funTerminates = Just b }
    setT def            = def

-- | Modify the clauses of a function.
modifyFunClauses :: QName -> ([Clause] -> [Clause]) -> TCM ()
modifyFunClauses q f =
  modifySignature $ updateDefinition q $ updateTheDef $ updateFunClauses f

-- | Lifts clauses to the top-level and adds them to definition.
addClauses :: QName -> [Clause] -> TCM ()
addClauses q cls = do
  tel <- getContextTelescope
  modifyFunClauses q (++ abstract tel cls)

addHaskellCode :: QName -> HaskellType -> HaskellCode -> TCM ()
addHaskellCode q hsTy hsDef = modifySignature $ updateDefinition q $ updateDefCompiledRep $ addHs
  -- TODO: sanity checking
  where
    addHs crep = crep { compiledHaskell = Just $ HsDefn hsTy hsDef }

addHaskellExport :: QName -> HaskellType -> String -> TCM ()
addHaskellExport q hsTy hsName = modifySignature $ updateDefinition q $ updateDefCompiledRep $ addHs
  -- TODO: sanity checking
  where
    addHs crep = crep { exportHaskell = Just (HsExport hsTy hsName)}

addHaskellType :: QName -> HaskellType -> TCM ()
addHaskellType q hsTy = modifySignature $ updateDefinition q $ updateDefCompiledRep $ addHs
  -- TODO: sanity checking
  where
    addHs crep = crep { compiledHaskell = Just $ HsType hsTy }

addEpicCode :: QName -> EpicCode -> TCM ()
addEpicCode q epDef = modifySignature $ updateDefinition q $ updateDefCompiledRep $ addEp
  -- TODO: sanity checking
  where
    addEp crep = crep { compiledEpic = Just epDef }

addJSCode :: QName -> String -> TCM ()
addJSCode q jsDef =
  case JS.parse jsDef of
    Left e ->
      modifySignature $ updateDefinition q $ updateDefCompiledRep $ addJS (Just e)
    Right s ->
      typeError (CompilationError ("Failed to parse ECMAScript (..." ++ s ++ ") for " ++ show q))
  where
    addJS e crep = crep { compiledJS = e }

markStatic :: QName -> TCM ()
markStatic q = modifySignature $ updateDefinition q $ mark
  where
    mark def@Defn{theDef = fun@Function{}} =
      def{theDef = fun{funStatic = True}}
    mark def = def

unionSignatures :: [Signature] -> Signature
unionSignatures ss = foldr unionSignature emptySignature ss
  where
    unionSignature (Sig a b c) (Sig a' b' c') =
      Sig (Map.union a a')
          (HMap.union b b')              -- definitions are unique (in at most one module)
          (HMap.unionWith mappend c c')  -- rewrite rules are accumulated

-- | Add a section to the signature.
addSection :: ModuleName -> Nat -> TCM ()
addSection m fv = do
  tel <- getContextTelescope
  let sec = Section tel fv
  modifySignature $ \sig -> sig { sigSections = Map.insert m sec $ sigSections sig }

-- | Lookup a section. If it doesn't exist that just means that the module
--   wasn't parameterised.
lookupSection :: ModuleName -> TCM Telescope
lookupSection m = do
  sig  <- sigSections <$> getSignature
  isig <- sigSections <$> getImportedSignature
  return $ maybe EmptyTel secTelescope $ Map.lookup m sig `mplus` Map.lookup m isig

-- Add display forms to all names @xn@ such that @x = x1 es1@, ... @xn-1 = xn esn@.
addDisplayForms :: QName -> TCM ()
addDisplayForms x = do
  def  <- getConstInfo x
  args <- getContextArgs
  add (drop (projectionArgs $ theDef def) args) x x []
  where
    add args top x vs0 = do
      def <- getConstInfo x
      let cs = defClauses def
      case cs of
        [ Clause{ namedClausePats = pats, clauseBody = b } ]
          | all (isVar . namedArg) pats
          , Just (m, Def y es) <- strip (b `apply` vs0)
          , Just vs <- mapM isApplyElim es -> do
              let ps = raise 1 $ map unArg vs
                  df = Display 0 ps $ DTerm $ Def top $ map Apply args
              reportSLn "tc.display.section" 20 $ "adding display form " ++ show y ++ " --> " ++ show top
                                                ++ "\n  " ++ show df
              addDisplayForm y df
              add args top y vs
        _ -> do
              let reason = case cs of
                    []    -> "no clauses"
                    _:_:_ -> "many clauses"
                    [ Clause{ clauseBody = b } ] -> case strip b of
                      Nothing -> "bad body"
                      Just (m, Def y es)
                        | m < length args -> "too few args"
                        | m > length args -> "too many args"
                        | otherwise       -> "args=" ++ show args ++ " es=" ++ show es
                      Just (m, v) -> "not a def body"
              reportSLn "tc.display.section" 30 $ "no display form from " ++ show x ++ " because " ++ reason
              return ()
    strip (Body v)   = return (0, unSpine v)
    strip  NoBody    = Nothing
    strip (Bind b)   = do
      (n, v) <- strip $ absBody b
      return (n + 1, ignoreSharing v)

    isVar VarP{} = True
    isVar _      = False

-- | Module application (followed by module parameter abstraction).
applySection
  :: ModuleName     -- ^ Name of new module defined by the module macro.
  -> Telescope      -- ^ Parameters of new module.
  -> ModuleName     -- ^ Name of old module applied to arguments.
  -> Args           -- ^ Arguments of module application.
  -> Ren QName      -- ^ Imported names (given as renaming).
  -> Ren ModuleName -- ^ Imported modules (given as renaming).
  -> TCM ()
applySection new ptel old ts rd rm = do
  reportSLn "tc.mod.apply" 10 $ render $ vcat
    [ text "applySection"
    , text "new  =" <+> text (show new)
    , text "ptel =" <+> text (show ptel)
    , text "old  =" <+> text (show old)
    , text "ts   =" <+> text (show ts)
    ]
  reportSLn "tc.mod.apply" 80 $ render $ vcat
    [ text "arguments:  " <+> text (show ts)
    ]
  mapM_ (copyDef ts) rd
  mapM_ (copySec ts) rm
  mapM_ computePolarity (map snd rd)
  where
    -- Andreas, 2013-10-29
    -- Here, if the name x is not imported, it persists as
    -- old, possibly out-of-scope name.
    -- This old name may used by the case split tactic, leading to
    -- names that cannot be printed properly.
    -- I guess it would make sense to mark non-imported names
    -- as such (out-of-scope) and let splitting fail if it would
    -- produce out-of-scope constructors.
    copyName x = fromMaybe x $ lookup x rd

    argsToUse new = do
      let m = mnameFromList $ commonPrefix (mnameToList old) (mnameToList new)
      reportSLn "tc.mod.apply" 80 $ "Common prefix: " ++ show m
      let ms = tail . map mnameFromList . inits . mnameToList $ m
      ps <- mapM (maybe 0 secFreeVars <.> getSection) ms
      reportSLn "tc.mod.apply" 80 $ "  params: " ++ show (zip ms ps)
      return $ sum ps

    copyDef :: Args -> (QName, QName) -> TCM ()
    copyDef ts (x, y) = do
      def <- getConstInfo x
      np  <- argsToUse (qnameModule x)
      copyDef' np def
      where
        copyDef' np d = do
          reportSLn "tc.mod.apply" 60 $ "making new def for " ++ show y ++ " from " ++ show x ++ " with " ++ show np ++ " args " ++ show abstr
          reportSLn "tc.mod.apply" 80 $
            "args = " ++ show ts' ++ "\n" ++
            "old type = " ++ prettyShow (defType d) ++ "\n" ++
            "new type = " ++ prettyShow t
          addConstant y =<< nd y
          makeProjection y
          -- Set display form for the old name if it's not a constructor.
{- BREAKS fail/Issue478
          -- Andreas, 2012-10-20 and if we are not an anonymous module
          -- unless (isAnonymousModuleName new || isCon || size ptel > 0) $ do
-}
          -- Issue1238: the copied def should be an 'instance' if the original
          -- def is one. Skip constructors since the original constructor will
          -- still work as an instance.
          unless isCon $ whenJust inst $ \ c -> addNamedInstance y c
          unless (isCon || size ptel > 0) $ do
            addDisplayForms y
          where
            ts' = take np ts
            t   = defType d `apply` ts'
            pol = defPolarity d `apply` ts'
            occ = defArgOccurrences d `apply` ts'
            rew = defRewriteRules d `apply` ts'
            inst = defInstance d
            abstr = defAbstract d
            -- the name is set by the addConstant function
            nd :: QName -> TCM Definition
            nd y = Defn (defArgInfo d) y t pol occ [] (-1) noCompiledRep rew inst <$> def  -- TODO: mutual block?
            oldDef = theDef d
            isCon  = case oldDef of { Constructor{} -> True ; _ -> False }
            mutual = case oldDef of { Function{funMutual = m} -> m              ; _ -> [] }
            extlam = case oldDef of { Function{funExtLam = e} -> e              ; _ -> Nothing }
            with   = case oldDef of { Function{funWith = w}   -> copyName <$> w ; _ -> Nothing }
            -- Andreas, 2015-05-11, to fix issue 1413:
            -- Even if we apply the record argument (must be @var 0@), we stay a projection.
            -- This is because we may abstract the record argument later again.
            -- See succeed/ProjectionNotNormalized.agda
            isVar0 t = case ignoreSharing $ unArg t of Var 0 [] -> True; _ -> False
            proj   = case oldDef of
              Function{funProjection = Just p@Projection{projIndex = n}}
                | size ts < n || (size ts == n && isVar0 (last ts))
                -> Just $ p { projIndex    = n - size ts
                            , projDropPars = projDropPars p `apply` ts
                            }
              _ -> Nothing
            def =
              case oldDef of
                Constructor{ conPars = np, conData = d } -> return $
                  oldDef { conPars = np - size ts'
                         , conData = copyName d
                         }
                Datatype{ dataPars = np, dataCons = cs } -> return $
                  oldDef { dataPars   = np - size ts'
                         , dataClause = Just cl
                         , dataCons   = map copyName cs
                         }
                Record{ recPars = np, recConType = t, recTel = tel } -> return $
                  oldDef { recPars    = np - size ts'
                         , recClause  = Just cl
                         , recConType = apply t ts
                         , recTel     = apply tel ts
                         }
                _ -> do
                  cc <- compileClauses Nothing [cl] -- Andreas, 2012-10-07 non need for record pattern translation
                  let newDef = Function
                        { funClauses        = [cl]
                        , funCompiled       = Just $ cc
                        , funDelayed        = NotDelayed
                        , funInv            = NotInjective
                        , funMutual         = mutual
                        , funAbstr          = ConcreteDef -- OR: abstr -- ?!
                        , funProjection     = proj
                        , funStatic         = False
                        , funCopy           = True
                        , funTerminates     = Just True
                        , funExtLam         = extlam
                        , funWith           = with
                        , funCopatternLHS   = isCopatternLHS [cl]
                        }
                  reportSLn "tc.mod.apply" 80 $ "new def for " ++ show x ++ "\n  " ++ show newDef
                  return newDef

            head = case oldDef of
                     Function{funProjection = Just Projection{ projDropPars = f}}
                       -> f
                     _ -> Def x []
            cl = Clause { clauseRange     = getRange $ defClauses d
                        , clauseTel       = EmptyTel
                        , clausePerm      = idP 0
                        , namedClausePats = []
                        , clauseBody      = Body $ head `apply` ts'
                        , clauseType      = Just $ defaultArg t
                        }

    copySec :: Args -> (ModuleName, ModuleName) -> TCM ()
    copySec ts (x, y) = do
      totalArgs <- argsToUse x
      tel       <- lookupSection x
      ptel      <- lookupSection $ mnameFromList $ init $ mnameToList x
      let parentParams = size ptel
          childParams  = size tel - parentParams
          argsToChild  = max 0 $ totalArgs - parentParams
      let fv = childParams - argsToChild
      reportSLn "tc.mod.apply" 80 $ "Copying section " ++ show x ++ " to " ++ show y
      reportSLn "tc.mod.apply" 80 $ "  free variables: " ++ show fv
      reportSLn "tc.mod.apply" 80 $ "  ts  = " ++ show ts
      reportSLn "tc.mod.apply" 80 $ "  tel = " ++ show (map (second unEl . unDom) $ telToList tel)
      reportSLn "tc.mod.apply" 80 $ "  ptel = " ++ show (map (second unEl . unDom) $ telToList ptel)
      reportSLn "tc.mod.apply" 80 $ "  np  = " ++ show totalArgs
      addCtxTel (apply tel $ take totalArgs ts) $ addSection y fv

-- | Add a display form to a definition (could be in this or imported signature).
addDisplayForm :: QName -> DisplayForm -> TCM ()
addDisplayForm x df = do
  d <- makeOpen df
  let add = updateDefinition x $ \ def -> def{ defDisplay = d : defDisplay def }
  modifyImportedSignature add
  modifySignature add

canonicalName :: QName -> TCM QName
canonicalName x = do
  def <- theDef <$> getConstInfo x
  case def of
    Constructor{conSrcCon = c}                                -> return $ conName c
    Record{recClause = Just (Clause{ clauseBody = body })}    -> canonicalName $ extract body
    Datatype{dataClause = Just (Clause{ clauseBody = body })} -> canonicalName $ extract body
    _                                                         -> return x
  where
    extract NoBody           = __IMPOSSIBLE__
    extract (Body (Def x _)) = x
    extract (Body (Shared p)) = extract (Body $ derefPtr p)
    extract (Body _)         = __IMPOSSIBLE__
    extract (Bind b)         = extract (unAbs b)

sameDef :: QName -> QName -> TCM (Maybe QName)
sameDef d1 d2 = do
  c1 <- canonicalName d1
  c2 <- canonicalName d2
  if (c1 == c2) then return $ Just c1 else return Nothing

-- | Can be called on either a (co)datatype, a record type or a
--   (co)constructor.
whatInduction :: QName -> TCM Induction
whatInduction c = do
  def <- theDef <$> getConstInfo c
  case def of
    Datatype{ dataInduction = i } -> return i
    Record{ recRecursive = False} -> return Inductive
    Record{ recInduction = i    } -> return $ fromMaybe Inductive i
    Constructor{ conInd = i }     -> return i
    _                             -> __IMPOSSIBLE__

-- | Does the given constructor come from a single-constructor type?
--
-- Precondition: The name has to refer to a constructor.
singleConstructorType :: QName -> TCM Bool
singleConstructorType q = do
  d <- theDef <$> getConstInfo q
  case d of
    Record {}                   -> return True
    Constructor { conData = d } -> do
      di <- theDef <$> getConstInfo d
      return $ case di of
        Record {}                  -> True
        Datatype { dataCons = cs } -> length cs == 1
        _                          -> __IMPOSSIBLE__
    _ -> __IMPOSSIBLE__

class (Functor m, Applicative m, Monad m) => HasConstInfo m where
  -- | Lookup the definition of a name. The result is a closed thing, all free
  --   variables have been abstracted over.
  getConstInfo :: QName -> m Definition
  -- | Lookup the rewrite rules with the given head symbol.
  getRewriteRulesFor :: QName -> m RewriteRules

{-# SPECIALIZE getConstInfo :: QName -> TCM Definition #-}

defaultGetRewriteRulesFor :: (Monad m) => m TCState -> QName -> m RewriteRules
defaultGetRewriteRulesFor getTCState q = do
  st <- getTCState
  let sig = st^.stSignature
      imp = st^.stImports
      look s = HMap.lookup q $ sigRewriteRules s
  return $ mconcat $ catMaybes [look sig, look imp]

instance HasConstInfo (TCMT IO) where
  getRewriteRulesFor = defaultGetRewriteRulesFor get
  getConstInfo q = join $ pureTCM $ \st env ->
    let defs  = sigDefinitions $ st^.stSignature
        idefs = sigDefinitions $ st^.stImports
    in case catMaybes [HMap.lookup q defs, HMap.lookup q idefs] of
        []  -> fail $ "Unbound name: " ++ show q ++ " " ++ showQNameId q
        [d] -> mkAbs env d
        ds  -> fail $ "Ambiguous name: " ++ show q
    where
      mkAbs env d
        | treatAbstractly' q' env =
          case makeAbstract d of
            Just d      -> return d
            Nothing     -> notInScope $ qnameToConcrete q
              -- the above can happen since the scope checker is a bit sloppy with 'abstract'
        | otherwise = return d
        where
          q' = case theDef d of
            -- Hack to make abstract constructors work properly. The constructors
            -- live in a module with the same name as the datatype, but for 'abstract'
            -- purposes they're considered to be in the same module as the datatype.
            Constructor{} -> dropLastModule q
            _             -> q

          dropLastModule q@QName{ qnameModule = m } =
            q{ qnameModule = mnameFromList $ ifNull (mnameToList m) __IMPOSSIBLE__ init }

instance (HasConstInfo m, Error err) => HasConstInfo (ExceptionT err m) where
  getConstInfo = lift . getConstInfo
  getRewriteRulesFor = lift . getRewriteRulesFor

{-# INLINE getConInfo #-}
getConInfo :: MonadTCM tcm => ConHead -> tcm Definition
getConInfo = liftTCM . getConstInfo . conName

-- | Look up the polarity of a definition.
getPolarity :: QName -> TCM [Polarity]
getPolarity q = defPolarity <$> getConstInfo q

-- | Look up polarity of a definition and compose with polarity
--   represented by 'Comparison'.
getPolarity' :: Comparison -> QName -> TCM [Polarity]
getPolarity' CmpEq  q = map (composePol Invariant) <$> getPolarity q -- return []
getPolarity' CmpLeq q = getPolarity q -- composition with Covariant is identity

-- | Set the polarity of a definition.
setPolarity :: QName -> [Polarity] -> TCM ()
setPolarity q pol = modifySignature $ updateDefinition q $ updateDefPolarity $ const pol

-- | Get argument occurrence info for argument @i@ of definition @d@ (never fails).
getArgOccurrence :: QName -> Nat -> TCM Occurrence
getArgOccurrence d i = do
  def <- getConstInfo d
  return $ case theDef def of
    Constructor{} -> StrictPos
    _             -> fromMaybe Mixed $ defArgOccurrences def !!! i

setArgOccurrences :: QName -> [Occurrence] -> TCM ()
setArgOccurrences d os = modifyArgOccurrences d $ const os

modifyArgOccurrences :: QName -> ([Occurrence] -> [Occurrence]) -> TCM ()
modifyArgOccurrences d f =
  modifySignature $ updateDefinition d $ updateDefArgOccurrences f

-- | Get the mutually recursive identifiers.
getMutual :: QName -> TCM [QName]
getMutual d = do
  def <- theDef <$> getConstInfo d
  return $ case def of
    Function {  funMutual = m } -> m
    Datatype { dataMutual = m } -> m
    Record   {  recMutual = m } -> m
    _ -> []

-- | Set the mutually recursive identifiers.
setMutual :: QName -> [QName] -> TCM ()
setMutual d m = modifySignature $ updateDefinition d $ updateTheDef $ \ def ->
  case def of
    Function{} -> def { funMutual = m }
    Datatype{} -> def {dataMutual = m }
    Record{}   -> def { recMutual = m }
    _          -> __IMPOSSIBLE__

-- | Check whether two definitions are mutually recursive.
mutuallyRecursive :: QName -> QName -> TCM Bool
mutuallyRecursive d d' = (d `elem`) <$> getMutual d'

-- | Why Maybe? The reason is that we look up all prefixes of a module to
--   compute number of parameters, and for hierarchical top-level modules,
--   A.B.C say, A and A.B do not exist.
getSection :: ModuleName -> TCM (Maybe Section)
getSection m = do
  sig  <- sigSections <$> getSignature
  isig <- sigSections <$> getImportedSignature
  return $ Map.lookup m sig <|> Map.lookup m isig

-- | Look up the number of free variables of a section. This is equal to the
--   number of parameters if we're currently inside the section and 0 otherwise.
getSecFreeVars :: ModuleName -> TCM Nat
getSecFreeVars m = do
  top <- currentModule
  case top `isSubModuleOf` m || top == m of
    True  -> maybe 0 secFreeVars <$> getSection m
    False -> return 0

-- | Compute the number of free variables of a module. This is the sum of
--   the free variables of its sections.
getModuleFreeVars :: ModuleName -> TCM Nat
getModuleFreeVars m = sum <$> ((:) <$> getAnonymousVariables m <*> mapM getSecFreeVars ms)
  where
    ms = map mnameFromList . inits . mnameToList $ m

-- | Compute the number of free variables of a defined name. This is the sum of
--   the free variables of the sections it's contained in.
getDefFreeVars :: QName -> TCM Nat
getDefFreeVars q = getModuleFreeVars (qnameModule q)

-- | Compute the context variables to apply a definition to.
freeVarsToApply :: QName -> TCM Args
freeVarsToApply x = genericTake <$> getDefFreeVars x <*> getContextArgs

-- | Instantiate a closed definition with the correct part of the current
--   context.
instantiateDef :: Definition -> TCM Definition
instantiateDef d = do
  vs  <- freeVarsToApply $ defName d
  verboseS "tc.sig.inst" 30 $ do
    ctx <- getContext
    m   <- currentModule
    reportSLn "tc.sig.inst" 30 $
      "instDef in " ++ show m ++ ": " ++ show (defName d) ++ " " ++
      unwords (map show . take (size vs) . reverse . map (fst . unDom) $ ctx)
  return $ d `apply` vs

-- | Give the abstract view of a definition.
makeAbstract :: Definition -> Maybe Definition
makeAbstract d =
  case defAbstract d of
    ConcreteDef -> return d
    AbstractDef -> do
      def <- makeAbs $ theDef d
      return d { defArgOccurrences = [] -- no positivity info for abstract things!
               , defPolarity       = [] -- no polarity info for abstract things!
               , theDef = def
               }
  where
    makeAbs Datatype   {} = Just Axiom
    makeAbs Function   {} = Just Axiom
    makeAbs Constructor{} = Nothing
    -- Andreas, 2012-11-18:  Make record constructor and projections abstract.
    makeAbs d@Record{}    = Just Axiom
    -- Q: what about primitive?
    makeAbs d             = Just d

-- | Enter abstract mode. Abstract definition in the current module are transparent.
inAbstractMode :: TCM a -> TCM a
inAbstractMode = local $ \e -> e { envAbstractMode = AbstractMode,
                                   envAllowDestructiveUpdate = False }
                                    -- Allowing destructive updates when seeing through
                                    -- abstract may break the abstraction.

-- | Not in abstract mode. All abstract definitions are opaque.
inConcreteMode :: TCM a -> TCM a
inConcreteMode = local $ \e -> e { envAbstractMode = ConcreteMode }

-- | Ignore abstract mode. All abstract definitions are transparent.
ignoreAbstractMode :: MonadReader TCEnv m => m a -> m a
ignoreAbstractMode = local $ \e -> e { envAbstractMode = IgnoreAbstractMode,
                                       envAllowDestructiveUpdate = False }
                                       -- Allowing destructive updates when ignoring
                                       -- abstract may break the abstraction.

-- | Enter concrete or abstract mode depending on whether the given identifier
--   is concrete or abstract.
inConcreteOrAbstractMode :: QName -> TCM a -> TCM a
inConcreteOrAbstractMode q cont = do
  -- Andreas, 2015-07-01: If we do not ignoreAbstractMode here,
  -- we will get ConcreteDef for abstract things, as they are turned into axioms.
  a <- ignoreAbstractMode $ defAbstract <$> getConstInfo q
  case a of
    AbstractDef -> inAbstractMode cont
    ConcreteDef -> inConcreteMode cont

-- | Check whether a name might have to be treated abstractly (either if we're
--   'inAbstractMode' or it's not a local name). Returns true for things not
--   declared abstract as well, but for those 'makeAbstract' will have no effect.
treatAbstractly :: MonadReader TCEnv m => QName -> m Bool
treatAbstractly q = asks $ treatAbstractly' q

-- | Andreas, 2015-07-01:
--   If the @current@ module is a weak suffix of the identifier module,
--   we can see through its abstract definition if we are abstract.
--   (Then @treatAbstractly'@ returns @False@).
--
--   If I am not mistaken, then we cannot see definitions in the @where@
--   block of an abstract function from the perspective of the function,
--   because then the current module is a strict prefix of the module
--   of the local identifier.
--   This problem is fixed by removing trailing anonymous module name parts
--   (underscores) from both names.
treatAbstractly' :: QName -> TCEnv -> Bool
treatAbstractly' q env = case envAbstractMode env of
  ConcreteMode       -> True
  IgnoreAbstractMode -> False
  AbstractMode       -> not $ current == m || current `isSubModuleOf` m
  where
    current = dropAnon $ envCurrentModule env
    m       = dropAnon $ qnameModule q
    dropAnon (MName ms) = MName $ reverse $ dropWhile isNoName $ reverse ms

-- | Get type of a constant, instantiated to the current context.
typeOfConst :: QName -> TCM Type
typeOfConst q = defType <$> (instantiateDef =<< getConstInfo q)

-- | Get relevance of a constant.
relOfConst :: QName -> TCM Relevance
relOfConst q = defRelevance <$> getConstInfo q

-- | Get colors of a constant.
colOfConst :: QName -> TCM [Color]
colOfConst q = defColors <$> getConstInfo q

-- | The name must be a datatype.
sortOfConst :: QName -> TCM Sort
sortOfConst q =
    do  d <- theDef <$> getConstInfo q
        case d of
            Datatype{dataSort = s} -> return s
            _                      -> fail $ "Expected " ++ show q ++ " to be a datatype."

-- | The number of parameters of a definition.
defPars :: Definition -> Int
defPars d = case theDef d of
    Axiom{}                  -> 0
    def@Function{}           -> projectionArgs def
    Datatype  {dataPars = n} -> n
    Record     {recPars = n} -> n
    Constructor{conPars = n} -> n
    Primitive{}              -> 0

-- | The number of dropped parameters for a definition.
--   0 except for projection(-like) functions and constructors.
droppedPars :: Definition -> Int
droppedPars d = case theDef d of
    Axiom{}                  -> 0
    def@Function{}           -> projectionArgs def
    Datatype  {dataPars = _} -> 0  -- not dropped
    Record     {recPars = _} -> 0  -- not dropped
    Constructor{conPars = n} -> n
    Primitive{}              -> 0

-- | Is it the name of a record projection?
{-# SPECIALIZE isProjection :: QName -> TCM (Maybe Projection) #-}
isProjection :: HasConstInfo m => QName -> m (Maybe Projection)
isProjection qn = isProjection_ . theDef <$> getConstInfo qn

isProjection_ :: Defn -> Maybe Projection
isProjection_ def =
  case def of
    Function { funProjection = result } -> result
    _                                   -> Nothing

-- | Returns @True@ if we are dealing with a proper projection,
--   i.e., not a projection-like function nor a record field value
--   (projection applied to argument).
isProperProjection :: Defn -> Bool
isProperProjection d = caseMaybe (isProjection_ d) False $ \ isP ->
  if projIndex isP <= 0 then False else isJust $ projProper isP

-- | Number of dropped initial arguments of a projection(-like) function.
projectionArgs :: Defn -> Int
projectionArgs = maybe 0 (max 0 . pred . projIndex) . isProjection_

-- | Check whether a definition uses copatterns.
usesCopatterns :: QName -> TCM Bool
usesCopatterns q = do
  d <- theDef <$> getConstInfo q
  return $ case d of
    Function{ funCopatternLHS = b } -> b
    _ -> False

-- | Apply a function @f@ to its first argument, producing the proper
--   postfix projection if @f@ is a projection.
applyDef :: QName -> I.Arg Term -> TCM Term
applyDef f a = do
  let fallback = return $ Def f [Apply a]
  caseMaybeM (isProjection f) fallback $ \ isP -> do
    if projIndex isP <= 0 then fallback else do
      -- Get the original projection, if existing.
      caseMaybe (projProper isP) fallback $ \ f' -> do
        return $ unArg a `applyE` [Proj f']

-- | @getDefType f t@ computes the type of (possibly projection-(like))
--   function @t@ whose first argument has type @t@.
--   The `parameters' for @f@ are extracted from @t@.
--   @Nothing@ if @f@ is projection(like) but
--   @t@ is not a data/record/axiom type.
--
--   Precondition: @t@ is reduced.
--
--   See also: 'Agda.TypeChecking.Datatypes.getConType'
getDefType :: QName -> Type -> TCM (Maybe Type)
getDefType f t = do
  def <- getConstInfo f
  let a = defType def
  -- if @f@ is not a projection (like) function, @a@ is the correct type
      fallback = return $ Just a
  caseMaybe (isProjection_ $ theDef def) fallback $
    \ (Projection{ projIndex = n }) -> if n <= 0 then fallback else do
      -- otherwise, we have to instantiate @a@ to the "parameters" of @f@
      let npars | n == 0    = __IMPOSSIBLE__
                | otherwise = n - 1
      -- we get the parameters from type @t@
      case ignoreSharing $ unEl t of
        Def d es -> do
          -- Andreas, 2013-10-22
          -- we need to check this @Def@ is fully reduced.
          -- If it is stuck due to disabled reductions
          -- (because of failed termination check),
          -- we will produce garbage parameters.
          flip (ifM $ eligibleForProjectionLike d) (return Nothing) $ do
            -- now we know it is reduced, we can safely take the parameters
            let pars = fromMaybe __IMPOSSIBLE__ $ allApplyElims $ take npars es
            -- pars <- maybe (return Nothing) return $ allApplyElims $ take npars es
            return $ Just $ a `apply` pars
        _ -> return Nothing
