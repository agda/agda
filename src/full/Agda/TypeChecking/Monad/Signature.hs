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
import qualified Agda.Utils.IO.Locale as LocIO

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
import Agda.TypeChecking.Free (freeIn)
import Agda.TypeChecking.Substitute
-- import Agda.TypeChecking.Pretty -- leads to cyclicity
import {-# SOURCE #-} Agda.TypeChecking.CompiledClause.Compile
import {-# SOURCE #-} Agda.TypeChecking.Polarity

import Agda.Utils.Monad
import Agda.Utils.Map as Map
import Agda.Utils.Size
import Agda.Utils.Permutation
import Agda.Utils.Pretty

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

-- | Add a constant to the signature. Lifts the definition to top level.
addConstant :: QName -> Definition -> TCM ()
addConstant q d = do
  reportSLn "tc.signature" 20 $ "adding constant " ++ show q ++ " to signature"
  tel <- getContextTelescope
  let tel' = killRange $ case theDef d of
	      Constructor{} -> hideTel tel
	      _		    -> tel
  let d' = abstract tel' $ d { defName = q }
  reportSLn "tc.signature" 30 $ "lambda-lifted definition = " ++ show d'
  modifySignature $ \sig -> sig
    { sigDefinitions = Map.insertWith (+++) q d' $ sigDefinitions sig }
  i <- currentMutualBlock
  setMutualBlock i q
  where
    new +++ old = new { defDisplay = defDisplay new ++ defDisplay old }

    hideTel  EmptyTel		      = EmptyTel
    hideTel (ExtendTel (Arg _ r t) tel) = ExtendTel (Arg Hidden r t) $ hideTel <$> tel

-- | Turn a definition into a projection if it looks like a projection.
makeProjection :: QName -> TCM ()
makeProjection x = inContext [] $ do
  reportSLn "tc.proj.like" 30 $ "Considering " ++ show x ++ " for projection likeness"
  defn <- getConstInfo x
  case theDef defn of
    -- Constructor-headed functions can't be projection-like (at the moment). The reason
    -- for this is that invoking constructor-headedness will circumvent the inference of
    -- the dropped arguments.
    -- Nor can abstract definitions be projection-like since they won't reduce
    -- outside the abstract block.
    def@Function{funProjection = Nothing, funClauses = cls, funInv = NotInjective,
                 funAbstr = ConcreteDef} -> do
      ps0 <- filterM validProj (candidateArgs [] (unEl $ defType defn))
      reportSLn "tc.proj.like" 30 $ if null ps0 then "  no candidates found"
                                                else "  candidates: " ++ show ps0
      ps <- return $ filter (checkOccurs cls . snd) ps0
      when (not (null ps0) && null ps) $ reportSLn "tc.proj.like" 50 $ "  occurs check failed\n    clauses = " ++ show cls
      case reverse ps of
        []         -> return ()
        (d, n) : _ -> do
          reportSLn "tc.proj.like" 10 $ show (defName defn) ++ " is projection like in argument " ++
                                        show n ++ " for type " ++ show d
          let cls' = map (rewriteClause n) cls
          cc <- compileClauses True cls'
          reportSLn "tc.proj.like" 20 $ "  rewrote clauses to\n    " ++ show cc
          let mapInv f NotInjective  = NotInjective
              mapInv f (Inverse inv) = Inverse (f inv)
              newDef = def
                       { funProjection     = Just (d, n + 1)
                       , funClauses        = cls'
                       , funCompiled       = cc
                       , funInv            = mapInv (Map.map $ rewriteClause n) $ funInv def
                       , funArgOccurrences = drop n $ funArgOccurrences def
                       , funPolarity       = drop n $ funPolarity def
                       }
          addConstant x $ defn{ theDef     = newDef
                              , defDisplay = [] }
    _ -> return ()
  where
    validProj (_, 0) = return False
    validProj (d, _) = do
      defn <- theDef <$> getConstInfo d
      return $ case defn of
        Datatype{} -> True
        Record{}   -> True
        Axiom{}    -> True
        _          -> False

    rewriteClause n cl@Clause{clausePerm = Perm m p} =
      cl{ clausePerm = Perm (m - fromIntegral n) $ map (subtract $ fromIntegral n) $ drop n p
        , clauseTel  = telFromList $ drop n $ telToList $ clauseTel cl
        , clausePats = drop n $ clausePats cl
        , clauseBody = dropB n $ clauseBody cl
        }
      where
        dropB 0 b          = b
        dropB _ NoBody     = NoBody
        dropB n (Bind b)   = dropB (n - 1) (absBody b)
        dropB n Body{}     = __IMPOSSIBLE__

    checkOccurs cls n = all (nonOccur n) cls

    nonOccur n Clause{clausePerm = Perm _ p, clausePats = ps, clauseBody = b} =
      and [ take n p == [0..fromIntegral n - 1]
          , onlyMatch n ps  -- projection-like functions are only allowed to match on the eliminatee
                            -- otherwise we may end up projecting from constructor applications, in
                            -- which case we can't reconstruct the dropped parameters
          , checkBody n b ]

    onlyMatch n ps = all (noMatch . unArg) $ ps0 ++ drop 1 ps1
      where
        (ps0, ps1) = splitAt n ps
        noMatch ConP{} = False
        noMatch LitP{} = False
        noMatch VarP{} = True
        noMatch DotP{} = True

    checkBody 0 _          = True
    checkBody _ NoBody     = True
    checkBody n (Bind b)   = not (0 `freeIn` absBody b) && checkBody (n - 1) (absBody b)
    checkBody _ Body{}     = __IMPOSSIBLE__

    candidateArgs vs (Fun (Arg _ _ (El _ (Def d us))) _)
      | vs == map unArg us = [(d, length vs)]
    candidateArgs vs (Pi (Arg r h (El _ (Def d us))) b)
      | vs == map unArg us = (d, length vs) : candidateRec vs b
    candidateArgs vs (Pi _ b) = candidateRec vs b
    candidateArgs _ _ = []

    candidateRec vs b = candidateArgs (Var (size vs) [] : vs) (unEl $ absBody b)

addHaskellCode :: QName -> HaskellType -> HaskellCode -> TCM ()
addHaskellCode q hsTy hsDef =
  -- TODO: sanity checking
  modifySignature $ \sig -> sig
  { sigDefinitions = Map.adjust addHs q $ sigDefinitions sig }
  where
    addHs def = def { defCompiledRep = (defCompiledRep def) { compiledHaskell = Just $ HsDefn hsTy hsDef } }

addHaskellType :: QName -> HaskellType -> TCM ()
addHaskellType q hsTy =
  -- TODO: sanity checking
  modifySignature $ \sig -> sig
  { sigDefinitions = Map.adjust addHs q $ sigDefinitions sig }
  where
    addHs def = def { defCompiledRep = (defCompiledRep def) { compiledHaskell = Just $ HsType hsTy } }

addEpicCode :: QName -> EpicCode -> TCM ()
addEpicCode q epDef =
  -- TODO: sanity checking
  modifySignature $ \sig -> sig
  { sigDefinitions = Map.adjust addEp q $ sigDefinitions sig }
  where
    --addEp def@Defn{theDef = con@Constructor{}} =
      --def{theDef = con{conHsCode = Just (hsTy, hsDef)}}
    addEp def = def { defCompiledRep = (defCompiledRep def) { compiledEpic = Just epDef } }

addJSCode :: QName -> String -> TCM ()
addJSCode q jsDef =
  case JS.parse jsDef of
    Left e ->
      modifySignature $ \sig -> sig
      { sigDefinitions = Map.adjust (addJS (Just e)) q $ sigDefinitions sig }
    Right s ->
      typeError (CompilationError ("Failed to parse ECMAScript (..." ++ s ++ ") for " ++ show q))
  where
    addJS e def = def{defCompiledRep = (defCompiledRep def){compiledJS = e}}

unionSignatures :: [Signature] -> Signature
unionSignatures ss = foldr unionSignature emptySignature ss
  where
    unionSignature (Sig a b) (Sig c d) = Sig (Map.union a c) (Map.union b d)

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
  add args x x []
  where
    add args top x ps = do
      cs <- defClauses <$> getConstInfo x
      case cs of
	[ Clause{ clauseBody = b } ]
	  | Just (m, Def y vs) <- strip b -> do
	      let ps' = raise 1 (map unArg vs) ++ ps
	      reportSLn "tc.display.section" 20 $ "adding display form " ++ show y ++ " --> " ++ show top
	      addDisplayForm y (Display 0 ps' $ DTerm $ Def top args)
	      add args top y ps'
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
      return (n + 1, v)

applySection ::
  ModuleName -> Telescope -> ModuleName -> Args ->
  Map QName QName -> Map ModuleName ModuleName -> TCM ()
applySection new ptel old ts rd rm = do
  sig  <- getSignature
  isig <- getImportedSignature
  let ss = getOld partOfOldM sigSections    [sig, isig]
      ds = getOld partOfOldD sigDefinitions [sig, isig]
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
  where
    getOld partOfOld fromSig sigs =
      Map.toList $ Map.filterKeys partOfOld $ Map.unions $ map fromSig sigs

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
          computePolarity y  -- AA: Polarity.sizePolarity needs also constructor names
	  -- Set display form for the old name if it's not a constructor.
	  unless (isCon || size ptel > 0) $ do
	    addDisplayForms y
      where
	t  = defType d `apply` ts
	-- the name is set by the addConstant function
	nd y = Defn (defRelevance d) y t [] (-1) noCompiledRep <$> def  -- TODO: mutual block?
        oldDef = theDef d
	isCon = case oldDef of
	  Constructor{} -> True
	  _		-> False
        getOcc d = case d of
          Function { funArgOccurrences  = os } -> os
          Datatype { dataArgOccurrences = os } -> os
          Record   { recArgOccurrences  = os } -> os
          _ -> []
        oldOcc = getOcc oldDef
	def  = case oldDef of
                Constructor{ conPars = np, conData = d } -> return $
                  oldDef { conPars = np - size ts, conData = copyName d }
                Datatype{ dataPars = np, dataCons = cs } -> return $
                  oldDef { dataPars = np - size ts, dataClause = Just cl, dataCons = map copyName cs
                         , dataArgOccurrences = drop (length ts) oldOcc }
                Record{ recPars = np, recConType = t, recTel = tel } -> return $
                  oldDef { recPars = np - size ts, recClause = Just cl
                         , recConType = apply t ts, recTel = apply tel ts
                         , recArgOccurrences = drop (length ts) oldOcc
                         }
		_ -> do
                  cc <- compileClauses True [cl]
                  let newDef = Function
                        { funClauses        = [cl]
                        , funCompiled       = cc
                        , funDelayed        = NotDelayed
                        , funInv            = NotInjective
                        , funPolarity       = []
                        , funArgOccurrences = drop (length ts') oldOcc
                        , funAbstr          = ConcreteDef
                        , funProjection     = proj
                        }
                  reportSLn "tc.mod.apply" 80 $ "new def for " ++ show x ++ "\n  " ++ show newDef
                  return newDef
                  where
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
    add df sig = sig { sigDefinitions = Map.adjust addDf x defs }
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
    extract NoBody	     = __IMPOSSIBLE__
    extract (Body (Def x _)) = x
    extract (Body _)	     = __IMPOSSIBLE__
    extract (Bind (Abs _ b)) = extract b

-- | Can be called on either a (co)datatype, a record type or a
--   (co)constructor.
whatInduction :: QName -> TCM Induction
whatInduction c = do
  def <- theDef <$> getConstInfo c
  case def of
    Datatype{ dataInduction = i } -> return i
    Record{}                      -> return Inductive
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
  in case smash (Map.lookup q defs) (Map.lookup q idefs) of
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
getPolarity q = do
  defn <- theDef <$> getConstInfo q
  case defn of
    Function{ funPolarity  = p } -> return p
    Datatype{ dataPolarity = p } -> return p
    Record{ recPolarity    = p } -> return p
    _                            -> return []

getPolarity' :: Comparison -> QName -> TCM [Polarity]
getPolarity' CmpEq _  = return []
getPolarity' CmpLeq q = getPolarity q

-- | Set the polarity of a definition.
setPolarity :: QName -> [Polarity] -> TCM ()
setPolarity q pol = do
  modifySignature setP
  where
    setP sig = sig { sigDefinitions = Map.adjust setPx q defs }
      where
	setPx def = def { theDef = setPd $ theDef def }
        setPd d   = case d of
          Function{} -> d { funPolarity  = pol }
          Datatype{} -> d { dataPolarity = pol }
          Record{}   -> d { recPolarity  = pol }
          _          -> d
	defs	  = sigDefinitions sig

getArgOccurrence :: QName -> Nat -> TCM Occurrence
getArgOccurrence d i = do
  def <- theDef <$> getConstInfo d
  return $ case def of
    Function { funArgOccurrences  = os } -> look i os
    Datatype { dataArgOccurrences = os } -> look i os
    Record   { recArgOccurrences  = os } -> look i os
    Constructor{}                        -> Positive
    _                                    -> Negative
  where
    look i os = (os ++ repeat Negative) !! fromIntegral i

setArgOccurrences :: QName -> [Occurrence] -> TCM ()
setArgOccurrences d os =
  modifySignature setO
  where
    setO sig = sig { sigDefinitions = Map.adjust setOx d defs }
      where
	setOx def = def { theDef = setOd $ theDef def }
        setOd d   = case d of
          Function{} -> d { funArgOccurrences  = os }
          Datatype{} -> d { dataArgOccurrences = os }
          Record{}   -> d { recArgOccurrences  = os }
          _          -> d
	defs	  = sigDefinitions sig


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
    liftIO $ LocIO.putStrLn $ "instDef in " ++ show m ++ ": " ++ show (defName d) ++ " " ++
			unwords (map show . take (size vs) . reverse . map (fst . unArg) $ ctx)
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
inAbstractMode = local $ \e -> e { envAbstractMode = AbstractMode }

-- | Not in abstract mode. All abstract definitions are opaque.
inConcreteMode :: TCM a -> TCM a
inConcreteMode = local $ \e -> e { envAbstractMode = ConcreteMode }

-- | Ignore abstract mode. All abstract definitions are transparent.
ignoreAbstractMode :: TCM a -> TCM a
ignoreAbstractMode = local $ \e -> e { envAbstractMode = IgnoreAbstractMode }

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
