{-# LANGUAGE CPP, PatternGuards #-}
module Agda.TypeChecking.Monad.Signature where

import Control.Arrow ((***))
import Control.Monad.State
import Control.Monad.Reader
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.List
import Data.Function

import Agda.Syntax.Abstract.Name
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Position

import qualified Agda.Compiler.JS.Parser as JS

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Context
import Agda.TypeChecking.Monad.Options
import Agda.TypeChecking.Monad.Env
import Agda.TypeChecking.Monad.Mutual
import Agda.TypeChecking.Monad.Open
import Agda.TypeChecking.Free (isBinderUsed)
import Agda.TypeChecking.Substitute
-- import Agda.TypeChecking.Pretty -- leads to cyclicity
import {-# SOURCE #-} Agda.TypeChecking.CompiledClause.Compile
import {-# SOURCE #-} Agda.TypeChecking.Polarity
import {-# SOURCE #-} Agda.TypeChecking.ProjectionLike

import Agda.Utils.Monad
import Agda.Utils.Map as Map
import Agda.Utils.Size
import Agda.Utils.Permutation
import Agda.Utils.Pretty
import qualified Agda.Utils.HashMap as HMap

#include "../../undefined.h"
import Agda.Utils.Impossible

modifySignature :: (Signature -> Signature) -> TCM ()
modifySignature f = modify $ \s -> s { stSignature = f $ stSignature s }

modifyImportedSignature :: (Signature -> Signature) -> TCM ()
modifyImportedSignature f = modify $ \s -> s { stImports = f $ stImports s }

getSignature :: TCM Signature
getSignature = gets stSignature

getImportedSignature :: TCM Signature
getImportedSignature = gets stImports

setSignature :: Signature -> TCM ()
setSignature sig = modifySignature $ const sig

setImportedSignature :: Signature -> TCM ()
setImportedSignature sig = modify $ \s -> s { stImports = sig }

withSignature :: Signature -> TCM a -> TCM a
withSignature sig m =
    do	sig0 <- getSignature
	setSignature sig
	r <- m
	setSignature sig0
        return r

-- * modifiers for parts of the signature

updateDefinition :: QName -> (Definition -> Definition) -> Signature -> Signature
updateDefinition q f sig = sig { sigDefinitions = HMap.adjust f q (sigDefinitions sig) }

updateTheDef :: (Defn -> Defn) -> (Definition -> Definition)
updateTheDef f def = def { theDef = f (theDef def) }

updateDefType :: (Type -> Type) -> (Definition -> Definition)
updateDefType f def = def { defType = f (defType def) }

updateDefArgOccurrences :: ([Occurrence] -> [Occurrence]) -> (Definition -> Definition)
updateDefArgOccurrences f def = def { defArgOccurrences = f (defArgOccurrences def) }

updateDefPolarity :: ([Polarity] -> [Polarity]) -> (Definition -> Definition)
updateDefPolarity f def = def { defPolarity = f (defPolarity def) }

-- | Add a constant to the signature. Lifts the definition to top level.
addConstant :: QName -> Definition -> TCM ()
addConstant q d = do
  reportSLn "tc.signature" 20 $ "adding constant " ++ show q ++ " to signature"
  tel <- getContextTelescope
  let tel' = killRange $ case theDef d of
	      Constructor{} -> fmap (mapDomHiding (const Hidden)) tel
	      _		    -> tel
  let d' = abstract tel' $ d { defName = q }
  reportSLn "tc.signature" 30 $ "lambda-lifted definition = " ++ show d'
  modifySignature $ \sig -> sig
    { sigDefinitions = HMap.insertWith (+++) q d' $ sigDefinitions sig }
  i <- currentOrFreshMutualBlock
  setMutualBlock i q
  where
    new +++ old = new { defDisplay = defDisplay new ++ defDisplay old }

addHaskellCode :: QName -> HaskellType -> HaskellCode -> TCM ()
addHaskellCode q hsTy hsDef =
  -- TODO: sanity checking
  modifySignature $ \sig -> sig
  { sigDefinitions = HMap.adjust addHs q $ sigDefinitions sig }
  where
    addHs def = def { defCompiledRep = (defCompiledRep def) { compiledHaskell = Just $ HsDefn hsTy hsDef } }

addHaskellType :: QName -> HaskellType -> TCM ()
addHaskellType q hsTy =
  -- TODO: sanity checking
  modifySignature $ \sig -> sig
  { sigDefinitions = HMap.adjust addHs q $ sigDefinitions sig }
  where
    addHs def = def { defCompiledRep = (defCompiledRep def) { compiledHaskell = Just $ HsType hsTy } }

addEpicCode :: QName -> EpicCode -> TCM ()
addEpicCode q epDef =
  -- TODO: sanity checking
  modifySignature $ \sig -> sig
  { sigDefinitions = HMap.adjust addEp q $ sigDefinitions sig }
  where
    --addEp def@Defn{theDef = con@Constructor{}} =
      --def{theDef = con{conHsCode = Just (hsTy, hsDef)}}
    addEp def = def { defCompiledRep = (defCompiledRep def) { compiledEpic = Just epDef } }

addJSCode :: QName -> String -> TCM ()
addJSCode q jsDef =
  case JS.parse jsDef of
    Left e ->
      modifySignature $ \sig -> sig
      { sigDefinitions = HMap.adjust (addJS (Just e)) q $ sigDefinitions sig }
    Right s ->
      typeError (CompilationError ("Failed to parse ECMAScript (..." ++ s ++ ") for " ++ show q))
  where
    addJS e def = def{defCompiledRep = (defCompiledRep def){compiledJS = e}}

markStatic :: QName -> TCM ()
markStatic q =
  modifySignature $ \sig -> sig
  { sigDefinitions = HMap.adjust mark q $ sigDefinitions sig }
  where
    mark def@Defn{theDef = fun@Function{}} =
      def{theDef = fun{funStatic = True}}
    mark def = def

unionSignatures :: [Signature] -> Signature
unionSignatures ss = foldr unionSignature emptySignature ss
  where
    unionSignature (Sig a b) (Sig c d) = Sig (Map.union a c) (HMap.union b d)

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
  args <- getContextArgs
  n    <- do
    proj <- isProjection x
    return $ case proj of
      Just (_, n) -> n
      Nothing     -> 0
  add (drop (n - 1) args) x x []
  where
    add args top x vs0 = do
      def <- getConstInfo x
      let cs = defClauses def
      case cs of
	[ Clause{ clausePats = pats, clauseBody = b } ]
	  | all (isVar . unArg) pats
          , Just (m, Def y vs) <- strip (b `apply` vs0) -> do
	      let ps = raise 1 (map unArg vs)
                  df = Display 0 ps $ DTerm $ Def top args
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
		      Just (m, Def y vs)
			| m < length args -> "too few args"
			| m > length args -> "too many args"
			| otherwise	      -> "args=" ++ show args ++ " vs=" ++ show vs
		      Just (m, v) -> "not a def body"
	      reportSLn "tc.display.section" 30 $ "no display form from" ++ show x ++ " because " ++ reason
	      return ()
    strip (Body v)   = return (0, v)
    strip  NoBody    = Nothing
    strip (Bind b)   = do
      (n, v) <- strip $ absBody b
      return (n + 1, ignoreSharing v)

    isVar VarP{} = True
    isVar _      = False

applySection ::
  ModuleName -> Telescope -> ModuleName -> Args ->
  Map QName QName -> Map ModuleName ModuleName -> TCM ()
applySection new ptel old ts rd rm = do
  sig  <- getSignature
  isig <- getImportedSignature
  let ss = getOld partOfOldM sigSections    [sig, isig]
      ds = getOldH partOfOldD sigDefinitions [sig, isig]
  reportSLn "tc.mod.apply" 10 $ render $ vcat
    [ text "applySection"
    , text "new  =" <+> text (show new)
    , text "ptel =" <+> text (show ptel)
    , text "old  =" <+> text (show old)
    , text "ts   =" <+> text (show ts)
    ]
  reportSLn "tc.mod.apply" 80 $ "sections:    " ++ show ss ++ "\n" ++
                                "definitions: " ++ show ds
  reportSLn "tc.mod.apply" 80 $ render $ vcat
    [ text "arguments:  " <+> text (show ts)
    ]
  mapM_ (copyDef ts) ds
  mapM_ (copySec ts) ss
  mapM_ computePolarity (Map.elems rd)
  where
    getOld partOfOld fromSig sigs =
      Map.toList $ Map.filterKeys partOfOld $ Map.unions $ map fromSig sigs
    getOldH partOfOld fromSig sigs =
      HMap.toList $ HMap.filterWithKey (const . partOfOld) $ HMap.unions $ map fromSig sigs

    partOfOldM x = x `isSubModuleOf` old
    partOfOldD x = x `isInModule`    old

    copyName x = maybe x id $ Map.lookup x rd

    copyDef :: Args -> (QName, Definition) -> TCM ()
    copyDef ts (x, d) = case Map.lookup x rd of
	Nothing -> return ()  -- if it's not in the renaming it was private and
			      -- we won't need it
	Just y	-> do
	  addConstant y =<< nd y
          makeProjection y
	  -- Set display form for the old name if it's not a constructor.
	  unless (isCon || size ptel > 0) $ do
	    addDisplayForms y
      where
	t   = defType d `apply` ts
        pol = defPolarity d `apply` ts
        occ = defArgOccurrences d `apply` ts
	-- the name is set by the addConstant function
	nd y = Defn (defRelevance d) y t pol occ [] (-1) noCompiledRep <$> def  -- TODO: mutual block?
        oldDef = theDef d
	isCon = case oldDef of
	  Constructor{} -> True
	  _		-> False
{- OLD
        getOcc d = case d of
          Function { funArgOccurrences  = os } -> os
          Datatype { dataArgOccurrences = os } -> os
          Record   { recArgOccurrences  = os } -> os
          _ -> []
        oldOcc = getOcc oldDef
-}
	def  = case oldDef of
                Constructor{ conPars = np, conData = d } -> return $
                  oldDef { conPars = np - size ts, conData = copyName d }
                Datatype{ dataPars = np, dataCons = cs } -> return $
                  oldDef { dataPars = np - size ts, dataClause = Just cl, dataCons = map copyName cs
                         {- , dataArgOccurrences = drop (length ts) oldOcc -} }
                Record{ recPars = np, recConType = t, recTel = tel } -> return $
                  oldDef { recPars = np - size ts, recClause = Just cl
                         , recConType = apply t ts, recTel = apply tel ts
                         {- , recArgOccurrences = drop (length ts) oldOcc -}
                         }
		_ -> do
                  cc <- compileClauses Nothing [cl] -- Andreas, 2012-10-07 non need for record pattern translation
                  let newDef = Function
                        { funClauses        = [cl]
                        , funCompiled       = cc
                        , funDelayed        = NotDelayed
                        , funInv            = NotInjective
{-
                        , funPolarity       = []
                        , funArgOccurrences = drop (length ts') oldOcc
-}
                        , funMutual         = mutual
                        , funAbstr          = ConcreteDef
                        , funProjection     = proj
                        , funStatic         = False
                        , funCopy           = True
                        }
                  reportSLn "tc.mod.apply" 80 $ "new def for " ++ show x ++ "\n  " ++ show newDef
                  return newDef
                  where
                    mutual = case oldDef of
                      Function{funMutual = m} -> m
                      _ -> []
                    proj = case oldDef of
                      Function{funProjection = Just (r, n)}
                        | size ts < n -> Just (r, n - size ts)
                      _ -> Nothing
        ts' | null ts   = []
            | otherwise = case oldDef of
                Function{funProjection = Just (_, n)}
                  | n == 0       -> __IMPOSSIBLE__
                  | otherwise    -> drop (n - 1) ts
                _ -> ts
	cl = Clause { clauseRange = getRange $ defClauses d
                    , clauseTel   = EmptyTel
                    , clausePerm  = idP 0
                    , clausePats  = []
                    , clauseBody  = Body $ Def x ts'
                    }

    copySec :: Args -> (ModuleName, Section) -> TCM ()
    copySec ts (x, sec) = case Map.lookup x rm of
	Nothing -> return ()  -- if it's not in the renaming it was private and
			      -- we won't need it
	Just y  ->
          addCtxTel (apply tel ts) $ addSection y 0
      where
	tel = secTelescope sec

addDisplayForm :: QName -> DisplayForm -> TCM ()
addDisplayForm x df = do
  d <- makeOpen df
  modifyImportedSignature (add d)
  modifySignature (add d)
  where
    add df sig = sig { sigDefinitions = HMap.adjust addDf x defs }
      where
	addDf def = def { defDisplay = df : defDisplay def }
	defs	  = sigDefinitions sig

canonicalName :: QName -> TCM QName
canonicalName x = do
  def <- theDef <$> getConstInfo x
  case def of
    Constructor{conSrcCon = c}                                -> return c
    Record{recClause = Just (Clause{ clauseBody = body })}    -> canonicalName $ extract body
    Datatype{dataClause = Just (Clause{ clauseBody = body })} -> canonicalName $ extract body
    _                                                         -> return x
  where
    extract NoBody           = __IMPOSSIBLE__
    extract (Body (Def x _)) = x
    extract (Body (Shared p)) = extract (Body $ derefPtr p)
    extract (Body _)         = __IMPOSSIBLE__
    extract (Bind b)         = extract (unAbs b)

-- | Can be called on either a (co)datatype, a record type or a
--   (co)constructor.
whatInduction :: QName -> TCM Induction
whatInduction c = do
  def <- theDef <$> getConstInfo c
  case def of
    Datatype{ dataInduction = i } -> return i
    Record{ recRecursive = False} -> return Inductive
    Record{ recInduction = i    } -> return i
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

-- | Lookup the definition of a name. The result is a closed thing, all free
--   variables have been abstracted over.
{-# SPECIALIZE getConstInfo :: QName -> TCM Definition #-}
getConstInfo :: MonadTCM tcm => QName -> tcm Definition
getConstInfo q = liftTCM $ join $ pureTCM $ \st env ->
  let defs  = sigDefinitions $ stSignature st
      idefs = sigDefinitions $ stImports st
      smash = (++) `on` maybe [] (:[])
  in case smash (HMap.lookup q defs) (HMap.lookup q idefs) of
      []  -> fail $ "Unbound name: " ++ show q ++ " " ++ showQNameId q
      [d] -> mkAbs env d
      ds  -> fail $ "Ambiguous name: " ++ show q
  where
    mkAbs env d
      | treatAbstractly' q' env =
        case makeAbstract d of
          Just d	-> return d
          Nothing	-> typeError $ NotInScope [qnameToConcrete q]
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
          q{ qnameModule = mnameFromList $ init' $ mnameToList m }

        init' [] = {-'-} __IMPOSSIBLE__
        init' xs = init xs

-- | Look up the polarity of a definition.
getPolarity :: QName -> TCM [Polarity]
getPolarity q = defPolarity <$> getConstInfo q

{- OLD
-- | Look up the polarity of a definition.
getPolarity :: QName -> TCM [Polarity]
getPolarity q = do
  defn <- theDef <$> getConstInfo q
  case defn of
    Function{ funPolarity  = p } -> return p
    Datatype{ dataPolarity = p } -> return p
    Record{ recPolarity    = p } -> return p
    _                            -> return []
-}

-- | Look up polarity of a definition and compose with polarity
--   represented by 'Comparison'.
getPolarity' :: Comparison -> QName -> TCM [Polarity]
getPolarity' CmpEq  q = map (composePol Invariant) <$> getPolarity q -- return []
getPolarity' CmpLeq q = getPolarity q -- composition with Covariant is identity

-- | Set the polarity of a definition.
setPolarity :: QName -> [Polarity] -> TCM ()
setPolarity q pol = modifySignature $ updateDefinition q $ updateDefPolarity $ const pol

{- OLD
-- | Set the polarity of a definition.
setPolarity :: QName -> [Polarity] -> TCM ()
setPolarity q pol = do
  modifySignature setP
  where
    setP sig = sig { sigDefinitions = HMap.adjust setPx q defs }
      where
	setPx def = def { theDef = setPd $ theDef def }
        setPd d   = case d of
          Function{} -> d { funPolarity  = pol }
          Datatype{} -> d { dataPolarity = pol }
          Record{}   -> d { recPolarity  = pol }
          _          -> d
	defs	  = sigDefinitions sig
-}

-- | Return a finite list of argument occurrences.
getArgOccurrences :: QName -> TCM [Occurrence]
getArgOccurrences d = defArgOccurrences <$> getConstInfo d

{- OLD
-- | Return a finite list of argument occurrences.
getArgOccurrences :: QName -> TCM [Occurrence]
getArgOccurrences d = do
  def <- theDef <$> getConstInfo d
  return $ getArgOccurrences_ def

getArgOccurrences_ :: Defn -> [Occurrence]
getArgOccurrences_ def = case def of
    Function { funArgOccurrences  = os } -> os
    Datatype { dataArgOccurrences = os } -> os
    Record   { recArgOccurrences  = os } -> os
    Constructor{}                        -> [] -- repeat StrictPos
    _                                    -> [] -- repeat Mixed
-}

getArgOccurrence :: QName -> Nat -> TCM Occurrence
getArgOccurrence d i = do
  def <- getConstInfo d
  return $ case theDef def of
    Constructor{} -> StrictPos
    _             -> (defArgOccurrences def ++ repeat Mixed) !! i

setArgOccurrences :: QName -> [Occurrence] -> TCM ()
setArgOccurrences d os =
  modifySignature $ updateDefinition d $ updateDefArgOccurrences $ const os

{- OLD
getArgOccurrence :: QName -> Nat -> TCM Occurrence
getArgOccurrence d i = do
  def <- theDef <$> getConstInfo d
  return $ case def of
    Function { funArgOccurrences  = os } -> look i os
    Datatype { dataArgOccurrences = os } -> look i os
    Record   { recArgOccurrences  = os } -> look i os
    Constructor{}                        -> StrictPos
    _                                    -> Mixed
  where
    look i os = (os ++ repeat Mixed) !! fromIntegral i

setArgOccurrences :: QName -> [Occurrence] -> TCM ()
setArgOccurrences d os =
  modifySignature setO
  where
    setO sig = sig { sigDefinitions = HMap.adjust setOx d defs }
      where
	setOx def = def { theDef = setOd $ theDef def }
        setOd d   = case d of
          Function{} -> d { funArgOccurrences  = os }
          Datatype{} -> d { dataArgOccurrences = os }
          Record{}   -> d { recArgOccurrences  = os }
          _          -> d
	defs	  = sigDefinitions sig
-}

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

-- | Look up the number of free variables of a section. This is equal to the
--   number of parameters if we're currently inside the section and 0 otherwise.
getSecFreeVars :: ModuleName -> TCM Nat
getSecFreeVars m = do
  sig  <- sigSections <$> getSignature
  isig <- sigSections <$> getImportedSignature
  top <- currentModule
  case top `isSubModuleOf` m || top == m of
    True  -> return $ maybe 0 secFreeVars $ Map.lookup m (Map.union sig isig)
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
    reportSLn "" 0 $ "instDef in " ++ show m ++ ": " ++ show (defName d) ++ " " ++
			unwords (map show . take (size vs) . reverse . map (fst . unDom) $ ctx)
  return $ d `apply` vs

-- | Give the abstract view of a definition.
makeAbstract :: Definition -> Maybe Definition
makeAbstract d = do def <- makeAbs $ theDef d
		    return d { theDef = def }
    where
	makeAbs Datatype   {dataAbstr = AbstractDef} = Just Axiom
	makeAbs Function   {funAbstr  = AbstractDef} = Just Axiom
	makeAbs Constructor{conAbstr  = AbstractDef} = Nothing
	makeAbs d                                    = Just d

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
ignoreAbstractMode :: TCM a -> TCM a
ignoreAbstractMode = local $ \e -> e { envAbstractMode = IgnoreAbstractMode,
                                       envAllowDestructiveUpdate = False }
                                       -- Allowing destructive updates when ignoring
                                       -- abstract may break the abstraction.

-- | Check whether a name might have to be treated abstractly (either if we're
--   'inAbstractMode' or it's not a local name). Returns true for things not
--   declared abstract as well, but for those 'makeAbstract' will have no effect.
treatAbstractly :: QName -> TCM Bool
treatAbstractly q = treatAbstractly' q <$> ask

treatAbstractly' :: QName -> TCEnv -> Bool
treatAbstractly' q env = case envAbstractMode env of
  ConcreteMode	     -> True
  IgnoreAbstractMode -> False
  AbstractMode	     -> not $ current == m || current `isSubModuleOf` m
  where
    current = envCurrentModule env
    m	    = qnameModule q

-- | get type of a constant
typeOfConst :: QName -> TCM Type
typeOfConst q = defType <$> (instantiateDef =<< getConstInfo q)

-- | get relevance of a constant
relOfConst :: QName -> TCM Relevance
relOfConst q = defRelevance <$> getConstInfo q

-- | The name must be a datatype.
sortOfConst :: QName -> TCM Sort
sortOfConst q =
    do	d <- theDef <$> getConstInfo q
	case d of
	    Datatype{dataSort = s} -> return s
	    _			   -> fail $ "Expected " ++ show q ++ " to be a datatype."

-- | Is it the name of a record projection?
isProjection :: QName -> TCM (Maybe (QName, Int))
isProjection qn = do
  def <- theDef <$> getConstInfo qn
  case def of
    Function { funProjection = result } -> return $ result
    _                                   -> return $ Nothing
