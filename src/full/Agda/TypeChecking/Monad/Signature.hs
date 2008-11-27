{-# LANGUAGE CPP, PatternGuards #-}
module Agda.TypeChecking.Monad.Signature where

import Control.Monad.State
import Control.Monad.Reader
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.List
import Data.Function
import qualified System.IO.UTF8 as UTF8

import Agda.Syntax.Abstract.Name
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Position

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Context
import Agda.TypeChecking.Monad.Options
import Agda.TypeChecking.Monad.Env
import Agda.TypeChecking.Monad.Mutual
import Agda.TypeChecking.Monad.Open
import Agda.TypeChecking.Substitute
import {-# SOURCE #-} Agda.TypeChecking.Polarity

import Agda.Utils.Monad
import Agda.Utils.Map as Map
import Agda.Utils.Size
import Agda.Utils.Permutation

#include "../../undefined.h"
import Agda.Utils.Impossible

modifySignature :: MonadTCM tcm => (Signature -> Signature) -> tcm ()
modifySignature f = modify $ \s -> s { stSignature = f $ stSignature s }

modifyImportedSignature :: MonadTCM tcm => (Signature -> Signature) -> tcm ()
modifyImportedSignature f = modify $ \s -> s { stImports = f $ stImports s }

getSignature :: MonadTCM tcm => tcm Signature
getSignature = liftTCM $ gets stSignature

getImportedSignature :: MonadTCM tcm => tcm Signature
getImportedSignature = liftTCM $ gets stImports

setSignature :: MonadTCM tcm => Signature -> tcm ()
setSignature sig = modifySignature $ const sig

setImportedSignature :: MonadTCM tcm => Signature -> tcm ()
setImportedSignature sig = liftTCM $ modify $ \s -> s { stImports = sig }

withSignature :: MonadTCM tcm => Signature -> tcm a -> tcm a
withSignature sig m =
    do	sig0 <- getSignature
	setSignature sig
	r <- m
	setSignature sig0
        return r

-- | Add a constant to the signature. Lifts the definition to top level.
addConstant :: MonadTCM tcm => QName -> Definition -> tcm ()
addConstant q d = liftTCM $ do
  tel <- getContextTelescope
  let tel' = killRange $ case theDef d of
	      Constructor{} -> hideTel tel
	      _		    -> tel
  modifySignature $ \sig -> sig
    { sigDefinitions = Map.insertWith (+++) q (abstract tel' d') $ sigDefinitions sig }
  i <- currentMutualBlock
  setMutualBlock i q
  where
    d' = d { defName = q }
    new +++ old = new { defDisplay = defDisplay new ++ defDisplay old }
    
    hideTel  EmptyTel		      = EmptyTel
    hideTel (ExtendTel (Arg _ t) tel) = ExtendTel (Arg Hidden t) $ hideTel <$> tel

addHaskellCode :: MonadTCM tcm => QName -> HaskellType -> HaskellCode -> tcm ()
addHaskellCode q hsTy hsDef =
  -- TODO: sanity checking
  modifySignature $ \sig -> sig
  { sigDefinitions = Map.adjust addHs q $ sigDefinitions sig }
  where
    addHs def@Defn{theDef = con@Constructor{}} =
      def{theDef = con{conHsCode = Just (hsTy, hsDef)}}
    addHs def@Defn{theDef = ax@Axiom{}} =
      def{theDef = ax{axHsDef = Just $ HsDefn hsTy hsDef}}
    addHs def = def

addHaskellType :: MonadTCM tcm => QName -> HaskellType -> tcm ()
addHaskellType q hsTy =
  -- TODO: sanity checking
  modifySignature $ \sig -> sig
  { sigDefinitions = Map.adjust addHs q $ sigDefinitions sig }
  where
    addHs def@Defn{theDef = ax@Axiom{}} =
      def{theDef = ax{axHsDef = Just $ HsType hsTy}}
    addHs def@Defn{theDef = d@Datatype{}} =
      def{theDef = d{dataHsType = Just hsTy}}
    addHs def = def

unionSignatures :: [Signature] -> Signature
unionSignatures ss = foldr unionSignature emptySignature ss
  where
    unionSignature (Sig a b) (Sig c d) = Sig (Map.union a c) (Map.union b d)

-- | Add a section to the signature.
addSection :: MonadTCM tcm => ModuleName -> Nat -> tcm ()
addSection m fv = do
  tel <- getContextTelescope
  let sec = Section tel fv
  modifySignature $ \sig -> sig { sigSections = Map.insert m sec $ sigSections sig }

-- | Lookup a section. If it doesn't exist that just means that the module
--   wasn't parameterised.
lookupSection :: MonadTCM tcm => ModuleName -> tcm Telescope
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
	[ Clause _ _ _ b ]
	  | Just (m, Def y vs) <- strip b
	  , m == length args && args `isPrefixOf` vs -> do
	      let ps' = raise 1 (map unArg vs) ++ ps
	      reportSLn "tc.section.apply.display" 20 $ "adding display form " ++ show y ++ " --> " ++ show top
	      addDisplayForm y (Display 0 ps' $ DTerm $ Def top args)
	      add args top y $ drop (length args) ps'
	_ -> do
	      let reason = case cs of
		    []    -> "no clauses"
		    _:_:_ -> "many clauses"
		    [ Clause _ _ _ b ] -> case strip b of
		      Nothing -> "bad body"
		      Just (m, Def y vs)
			| m < length args -> "too few args"
			| m > length args -> "too many args"
			| otherwise	      -> "args=" ++ unwords (map var args) ++ " vs=" ++ unwords (map var vs)
			  where
			    var (Arg h x) = hid h $ case x of
			      Var i []	-> show i
			      MetaV _ _	-> "?"
			      _		-> "_"
			    hid NotHidden s = s
			    hid Hidden    s = "{" ++ s ++ "}"
		      Just (m, v) -> "not a def body"
	      reportSLn "tc.section.apply.display" 30 $ "no display form from" ++ show x ++ " because " ++ reason
	      return ()
    strip (Body v)   = return (0, v)
    strip  NoBody    = Nothing
    strip (NoBind b) = Nothing
    strip (Bind b)   = do
      (n, v) <- strip $ absBody b
      return (n + 1, v)

applySection ::
  MonadTCM tcm => ModuleName -> Telescope -> ModuleName -> Args ->
  Map QName QName -> Map ModuleName ModuleName -> tcm ()
applySection new ptel old ts rd rm = liftTCM $ do
  sig  <- getSignature
  isig <- getImportedSignature
  let ss = Map.toList $ Map.filterKeys partOfOldM $ sigSections sig `Map.union` sigSections isig
      ds = Map.toList $ Map.filterKeys partOfOldD $ sigDefinitions sig `Map.union` sigDefinitions isig
  mapM_ (copyDef ts) ds
  mapM_ (copySec ts) ss
  where
    partOfOldM x = x `isSubModuleOf` old
    partOfOldD x = x `isInModule`    old

    copyName x = maybe x id $ Map.lookup x rd

    copyDef :: Args -> (QName, Definition) -> TCM ()
    copyDef ts (x, d) = case Map.lookup x rd of
	Nothing -> return ()  -- if it's not in the renaming it was private and
			      -- we won't need it
	Just y	-> do
	  addConstant y (nd y)
          computePolarity y
	  -- Set display form for the old name if it's not a constructor.
	  unless (isCon || size ptel > 0) $ do
	    addDisplayForms y
      where
	t  = defType d `apply` ts
	-- the name is set by the addConstant function
	nd y = Defn y t [] (-1) def  -- TODO: mutual block?
        oldDef = theDef d
	isCon = case oldDef of
	  Constructor{} -> True
	  _		-> False
        -- TODO: compute polarity for the new definition
	def  = case oldDef of
                Constructor{ conPars = np, conData = d } ->
                  oldDef { conPars = np - size ts, conData = copyName d }
                Datatype{ dataPars = np, dataCons = cs } ->
                  oldDef { dataPars = np - size ts, dataClause = Just cl, dataCons = map copyName cs }
                Record{ recPars = np, recTel = tel } ->
                  oldDef { recPars = np - size ts, recClause = Just cl, recTel = apply tel ts }
		_                           ->
                  Function { funClauses        = [cl]
                           , funRecursion      = Recursive
                           , funInv            = NotInjective
                           , funPolarity       = []
                           , funArgOccurrences = []
                           , funAbstr          = ConcreteDef
                           }
	cl = Clause EmptyTel (idP 0) [] $ Body $ Def x ts

    copySec :: Args -> (ModuleName, Section) -> TCM ()
    copySec ts (x, sec) = case Map.lookup x rm of
	Nothing -> return ()  -- if it's not in the renaming it was private and
			      -- we won't need it
	Just y  -> addCtxTel (apply tel ts) $ addSection y 0
      where
	tel = secTelescope sec

addDisplayForm :: MonadTCM tcm => QName -> DisplayForm -> tcm ()
addDisplayForm x df = do
  d <- makeOpen df
  modifyImportedSignature (add d)
  modifySignature (add d)
  where
    add df sig = sig { sigDefinitions = Map.adjust addDf x defs }
      where
	addDf def = def { defDisplay = df : defDisplay def }
	defs	  = sigDefinitions sig

canonicalName :: MonadTCM tcm => QName -> tcm QName
canonicalName x = do
  def <- theDef <$> getConstInfo x
  case def of
    Constructor{conSrcCon = c}                      -> return c
    Record{recClause = Just (Clause _ _ _ body)}    -> canonicalName $ extract body
    Datatype{dataClause = Just (Clause _ _ _ body)} -> canonicalName $ extract body
    _                                               -> return x
  where
    extract NoBody	     = __IMPOSSIBLE__
    extract (Body (Def x _)) = x
    extract (Body _)	     = __IMPOSSIBLE__
    extract (Bind (Abs _ b)) = extract b
    extract (NoBind b)	     = extract b

whatRecursion :: MonadTCM tcm => QName -> tcm (Maybe Recursion)
whatRecursion f = do
  def <- theDef <$> getConstInfo f
  case def of
    Function{ funRecursion = r, funClauses = cl }
      | any hasRHS cl -> return $ Just r
      | otherwise     -> return Nothing
    _                            -> return $ Just Recursive
  where
    hasRHS (Clause _ _ _ b) = hasBody b
    hasBody (Body _)   = True
    hasBody NoBody     = False
    hasBody (Bind b)   = hasBody $ absBody b
    hasBody (NoBind b) = hasBody b

-- | Can be called on either a (co)datatype or a (co)constructor.
whatInduction :: MonadTCM tcm => QName -> tcm Induction
whatInduction c = do
  def <- theDef <$> getConstInfo c
  case def of
    Datatype{ dataInduction = i } -> return i
    Constructor{ conData = d }    -> whatInduction d
    _                             -> return Inductive   -- fail instead?

-- | Lookup the definition of a name. The result is a closed thing, all free
--   variables have been abstracted over.
getConstInfo :: MonadTCM tcm => QName -> tcm Definition
getConstInfo q = liftTCM $ do
  ab    <- treatAbstractly q
  defs  <- sigDefinitions <$> getSignature
  idefs <- sigDefinitions <$> getImportedSignature
  let smash = (++) `on` maybe [] (:[])
  case smash (Map.lookup q defs) (Map.lookup q idefs) of
      []  -> fail $ show (getRange q) ++ ": no such name " ++ show q
      [d] -> mkAbs ab d
      ds  -> fail $ show (getRange q) ++ ": ambiguous name " ++ show q
  where
    mkAbs True d =
      case makeAbstract d of
	Just d	-> return d
	Nothing	-> typeError $ NotInScope [qnameToConcrete q]
	  -- the above can happen since the scope checker is a bit sloppy with 'abstract'
    mkAbs False d = return d

-- | Look up the polarity of a definition.
getPolarity :: MonadTCM tcm => QName -> tcm [Polarity]
getPolarity q = liftTCM $ do
  defn <- theDef <$> getConstInfo q
  case defn of
    Function{ funPolarity  = p } -> return p
    Datatype{ dataPolarity = p } -> return p
    Record{ recPolarity    = p } -> return p
    _                            -> return []

getPolarity' :: MonadTCM tcm => Comparison -> QName -> tcm [Polarity]
getPolarity' CmpEq _  = return []
getPolarity' CmpLeq q = getPolarity q

-- | Set the polarity of a definition.
setPolarity :: MonadTCM tcm => QName -> [Polarity] -> tcm ()
setPolarity q pol = liftTCM $ do
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

getArgOccurrence :: MonadTCM tcm => QName -> Nat -> tcm Occurrence
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

setArgOccurrences :: MonadTCM tcm => QName -> [Occurrence] -> tcm ()
setArgOccurrences d os = liftTCM $
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
getSecFreeVars :: MonadTCM tcm => ModuleName -> tcm Nat
getSecFreeVars m = do
  sig <- sigSections <$> getSignature
  top <- currentModule
  case top `isSubModuleOf` m || top == m of
    True  -> return $ maybe 0 secFreeVars $ Map.lookup m sig
    False -> return 0

-- | Compute the number of free variables of a defined name. This is the sum of
--   the free variables of the sections it's contained in.
getDefFreeVars :: MonadTCM tcm => QName -> tcm Nat
getDefFreeVars q = sum <$> ((:) <$> getAnonymousVariables m <*> mapM getSecFreeVars ms)
  where
    m  = qnameModule q
    ms = map mnameFromList . inits . mnameToList $ m

-- | Compute the context variables to apply a definition to.
freeVarsToApply :: MonadTCM tcm => QName -> tcm Args
freeVarsToApply x = genericTake <$> getDefFreeVars x <*> getContextArgs

-- | Instantiate a closed definition with the correct part of the current
--   context.
instantiateDef :: MonadTCM tcm => Definition -> tcm Definition
instantiateDef d = do
  vs  <- freeVarsToApply $ defName d
  verboseS "tc.sig.inst" 30 $ do
    ctx <- getContext
    m   <- currentModule
    liftIO $ UTF8.putStrLn $ "instDef in " ++ show m ++ ": " ++ show (defName d) ++ " " ++
			unwords (map show . take (size vs) . reverse . map (fst . unArg) $ ctx)
  return $ d `apply` vs

-- | Give the abstract view of a definition.
makeAbstract :: Definition -> Maybe Definition
makeAbstract d = do def <- makeAbs $ theDef d
		    return d { theDef = def }
    where
	makeAbs Datatype   {dataAbstr = AbstractDef} = Just $ Axiom Nothing
	makeAbs Function   {funAbstr  = AbstractDef} = Just $ Axiom Nothing
	makeAbs Constructor{conAbstr  = AbstractDef} = Nothing
	makeAbs d                                    = Just d

-- | Enter abstract mode. Abstract definition in the current module are transparent.
inAbstractMode :: MonadTCM tcm => tcm a -> tcm a
inAbstractMode = local $ \e -> e { envAbstractMode = AbstractMode }

-- | Not in abstract mode. All abstract definitions are opaque.
inConcreteMode :: MonadTCM tcm => tcm a -> tcm a
inConcreteMode = local $ \e -> e { envAbstractMode = ConcreteMode }

-- | Ignore abstract mode. All abstract definitions are transparent.
ignoreAbstractMode :: MonadTCM tcm => tcm a -> tcm a
ignoreAbstractMode = local $ \e -> e { envAbstractMode = IgnoreAbstractMode }

-- | Check whether a name might have to be treated abstractly (either if we're
--   'inAbstractMode' or it's not a local name). Returns true for things not
--   declared abstract as well, but for those 'makeAbstract' will have no effect.
treatAbstractly :: MonadTCM tcm => QName -> tcm Bool
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
typeOfConst :: MonadTCM tcm => QName -> tcm Type
typeOfConst q = defType <$> (instantiateDef =<< getConstInfo q)

-- | The name must be a datatype.
sortOfConst :: MonadTCM tcm => QName -> tcm Sort
sortOfConst q =
    do	d <- theDef <$> getConstInfo q
	case d of
	    Datatype{dataSort = s} -> return s
	    _			   -> fail $ "Expected " ++ show q ++ " to be a datatype."

