{-# LANGUAGE CPP, FlexibleContexts #-}

-- | Generates data used for precise syntax highlighting.

module Agda.Interaction.Highlighting.Generate
  ( generateSyntaxInfo
  , generateErrorInfo
  , highlightInteractively
  , highlightAsTypeChecked
  , Agda.Interaction.Highlighting.Generate.tests
  )
  where

import Agda.Interaction.FindFile
import Agda.Interaction.Response (Response(Resp_HighlightingInfo))
import Agda.Interaction.Highlighting.Emacs   hiding (tests)
import Agda.Interaction.Highlighting.Precise hiding (tests)
import Agda.Interaction.Highlighting.Range   hiding (tests)
import Agda.Interaction.EmacsCommand
import qualified Agda.TypeChecking.Errors as E
import Agda.TypeChecking.MetaVars (isBlockedTerm)
import Agda.TypeChecking.Monad.Options (reportSLn)
import Agda.TypeChecking.Monad
  hiding (MetaInfo, Primitive, Constructor, Record, Function, Datatype)
import qualified Agda.TypeChecking.Monad as M
import qualified Agda.TypeChecking.Reduce as R
import qualified Agda.Syntax.Abstract as A
import qualified Agda.Syntax.Common as SC
import qualified Agda.Syntax.Concrete as C
import qualified Agda.Syntax.Info as SI
import qualified Agda.Syntax.Internal as I
import qualified Agda.Syntax.Literal as L
import qualified Agda.Syntax.Parser as Pa
import qualified Agda.Syntax.Parser.Tokens as T
import qualified Agda.Syntax.Position as P
import qualified Agda.Syntax.Scope.Base as S
import qualified Agda.Syntax.Translation.ConcreteToAbstract as CA
import Agda.Utils.List
import Agda.Utils.TestHelpers
import Agda.Utils.HashMap (HashMap)
import qualified Agda.Utils.HashMap as HMap
import Control.Monad
import Control.Monad.Trans
import Control.Monad.State
import Control.Monad.Reader
import Control.Applicative
import Data.Monoid
import Data.Function
import Data.Generics.Geniplate
import Agda.Utils.FileName
import qualified Agda.Utils.IO.UTF8 as UTF8
import Agda.Utils.Monad
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.List ((\\), isPrefixOf)
import qualified Data.Foldable as Fold (toList, fold, foldMap)
import System.Directory
import System.IO

import Agda.Utils.Impossible
#include "../../undefined.h"

-- | Highlights the given thing first as being type-checked, and then,
-- once the computation has finished successfully, as having been
-- type-checked. Returns the result of the computation.
--
-- (The highlighting is only performed when
-- 'envInteractiveHighlighting' is @True@.)

highlightInteractively
  :: (P.HasRange r, MonadTCM tcm)
  => r
     -- ^ The thing.
  -> tcm a
     -- ^ The computation.
  -> tcm a
highlightInteractively x m = do
  highlightAsTypeChecked False x
  result <- m
  highlightAsTypeChecked True x
  return result

-- | Highlights the given thing as being/having been type-checked.
--
-- But only if 'envInteractiveHighlighting' is @True@.

highlightAsTypeChecked
  :: (P.HasRange r, MonadTCM tcm)
  => Bool
     -- ^ Has the code been type-checked?
  -> r
     -- ^ The thing.
  -> tcm ()
highlightAsTypeChecked typeChecked x =
  whenM (envInteractiveHighlighting <$> ask) $
    unless (null $ ranges file) $
      liftTCM $ do
        st <- get
        liftIO $ stInteractionOutputCallback st $ Resp_HighlightingInfo file
  where
  file =
    singletonC (P.continuousPerLine $ P.getRange x)
               (mempty { otherAspects = [aspect] })
  aspect = if typeChecked then TypeChecked else TypeChecks

-- | Generates syntax highlighting information for an error,
-- represented as a range and an optional string. The error range is
-- completed so that there are no gaps in it.
--
-- Nothing is generated unless the file name component of the range is
-- defined.

generateErrorInfo :: P.Range -> Maybe String -> Maybe HighlightingInfo
generateErrorInfo r s =
  case P.rStart r of
    Nothing                                          -> Nothing
    Just (P.Pn { P.srcFile = Nothing })              -> Nothing
    Just (P.Pn { P.srcFile = Just f, P.posPos = p }) ->
      Just $ compress $ generateErrorFile r s

-- | Generates syntax highlighting information for an error,
-- represented as a range and an optional string. The error range is
-- completed so that there are no gaps in it.

generateErrorFile :: P.Range -> Maybe String -> File
generateErrorFile r s =
  singleton (P.continuousPerLine r)
            (mempty { otherAspects = [Error]
                    , note         = s
                    })

-- | Generates syntax highlighting information.

generateSyntaxInfo
  :: AbsolutePath          -- ^ The module to highlight.
  -> Maybe TCErr           -- ^ 'Nothing' if the module has been
                           --   successfully type checked (perhaps
                           --   with warnings), otherwise the
                           --   offending error.
                           --
                           --   Precondition: The range of the error
                           --   must match the file name given in the
                           --   previous argument.
  -> CA.TopLevelInfo       -- ^ The abstract syntax of the module.
  -> [M.TerminationError]  -- ^ Termination checking problems.
  -> TCM HighlightingInfo
generateSyntaxInfo file mErr top termErrs = do
  reportSLn "import.iface.create" 15  $
      "Generating syntax info for " ++ filePath file ++ ' ' : maybe "(No TCErr)" (const "(with TCErr)") mErr ++ "."

  M.withScope_ (CA.insideScope top) $ M.ignoreAbstractMode $ do
    modMap <- sourceToModule
    tokens <- liftIO $ Pa.parseFile' Pa.tokensParser file
    kinds  <- nameKinds mErr decls
    let nameInfo = mconcat $ map (generate modMap file kinds) names
    -- Constructors are only highlighted after type checking, since they
    -- can be overloaded.
    constructorInfo <- case mErr of
      Nothing -> generateConstructorInfo modMap file kinds decls
      Just _  -> return mempty
    metaInfo <- case mErr of
      Nothing -> computeUnsolvedMetaWarnings
      Just _  -> return mempty
    constraintInfo <- case mErr of
      Nothing -> computeUnsolvedConstraints
      Just _  -> return mempty
    errorInfo <- case mErr of
      Nothing -> return mempty
      Just e  -> let r = P.getRange e in
        case P.rStart r of
          Just p | P.srcFile p == Just file ->
            generateErrorFile r . Just <$> E.prettyError e
          _ -> __IMPOSSIBLE__
    -- theRest needs to be placed before nameInfo here since record
    -- field declarations contain QNames. constructorInfo also needs
    -- to be placed before nameInfo since, when typechecking is done,
    -- constructors are included in both lists. Finally tokInfo is
    -- placed last since token highlighting is more crude than the
    -- others.
    return $ compress $ mconcat
      [ errorInfo
      , constructorInfo
      , theRest modMap
      , nameInfo
      , metaInfo
      , constraintInfo
      , termInfo
      , tokInfo tokens
      ]
  where
    decls = CA.topLevelDecls top

    -- Converts an aspect and a range to a file.
    aToF a r = singleton r (mempty { aspect = Just a })

    tokInfo = Fold.foldMap tokenToFile
      where
      tokenToFile :: T.Token -> File
      tokenToFile (T.TokSetN (i, _))               = aToF PrimitiveType (P.getRange i)
      tokenToFile (T.TokKeyword T.KwSet  i)        = aToF PrimitiveType (P.getRange i)
      tokenToFile (T.TokKeyword T.KwProp i)        = aToF PrimitiveType (P.getRange i)
      tokenToFile (T.TokKeyword T.KwForall i)      = aToF Symbol (P.getRange i)
      tokenToFile (T.TokKeyword _ i)               = aToF Keyword (P.getRange i)
      tokenToFile (T.TokSymbol  _ i)               = aToF Symbol (P.getRange i)
      tokenToFile (T.TokLiteral (L.LitInt    r _)) = aToF Number r
      tokenToFile (T.TokLiteral (L.LitFloat  r _)) = aToF Number r
      tokenToFile (T.TokLiteral (L.LitString r _)) = aToF String r
      tokenToFile (T.TokLiteral (L.LitChar   r _)) = aToF String r
      tokenToFile (T.TokLiteral (L.LitQName  r _)) = aToF String r
      tokenToFile (T.TokComment (i, _))            = aToF Comment (P.getRange i)
      tokenToFile (T.TokTeX (i, _))                = aToF Comment (P.getRange i)
      tokenToFile (T.TokId {})                     = mempty
      tokenToFile (T.TokQId {})                    = mempty
      tokenToFile (T.TokString {})                 = mempty
      tokenToFile (T.TokDummy {})                  = mempty
      tokenToFile (T.TokEOF {})                    = mempty

    termInfo = functionDefs `mappend` callSites
      where
      m            = mempty { otherAspects = [TerminationProblem] }
      functionDefs = Fold.foldMap (\x -> singleton (bindingSite x) m) $
                     concatMap M.termErrFunctions termErrs
      callSites    = Fold.foldMap (\r -> singleton r m) $
                     concatMap (map M.callInfoRange . M.termErrCalls) termErrs

    names :: [A.AmbiguousQName]
    names =
      (map (A.AmbQ . (:[])) $
       filter (not . extendedLambda) $
       universeBi decls) ++
      universeBi decls
      where
      extendedLambda :: A.QName -> Bool
      extendedLambda n = extendlambdaname `isPrefixOf` show (A.qnameName n)

    -- Bound variables, dotted patterns, record fields, module names,
    -- the "as" and "to" symbols.
    theRest modMap = mconcat
      [ Fold.foldMap getFieldDecl   $ universeBi decls
      , Fold.foldMap getVarAndField $ universeBi decls
      , Fold.foldMap getLet         $ universeBi decls
      , Fold.foldMap getLam         $ universeBi decls
      , Fold.foldMap getTyped       $ universeBi decls
      , Fold.foldMap getPattern     $ universeBi decls
      , Fold.foldMap getModuleName  $ universeBi decls
      , Fold.foldMap getModuleInfo  $ universeBi decls
      ]
      where
      bound n = nameToFile modMap file []
                           (A.nameConcrete n)
                           (\isOp -> mempty { aspect = Just $ Name (Just Bound) isOp })
                           (Just $ A.nameBindingSite n)
      field m n = nameToFile modMap file m n
                             (\isOp -> mempty { aspect = Just $ Name (Just Field) isOp })
                             Nothing
      asName n = nameToFile modMap file []
                            n
                            (\isOp -> mempty { aspect = Just $ Name (Just Module) isOp })
                            Nothing
      mod isTopLevelModule n =
        nameToFile modMap file []
                   (A.nameConcrete n)
                   (\isOp -> mempty { aspect = Just $ Name (Just Module) isOp })
                   (Just $ (if isTopLevelModule then P.beginningOfFile else id)
                             (A.nameBindingSite n))

      getVarAndField :: A.Expr -> File
      getVarAndField (A.Var x)    = bound x
      getVarAndField (A.Rec _ fs) = mconcat $ map (field [] . fst) fs
      getVarAndField _            = mempty

      getLet :: A.LetBinding -> File
      getLet (A.LetBind _ _ x _ _) = bound x
      getLet A.LetApply{}          = mempty
      getLet A.LetOpen{}           = mempty

      getLam :: A.LamBinding -> File
      getLam (A.DomainFree _ _ x) = bound x
      getLam (A.DomainFull {})  = mempty

      getTyped :: A.TypedBinding -> File
      getTyped (A.TBind _ xs _) = mconcat $ map bound xs
      getTyped (A.TNoBind {})   = mempty

      getPattern :: A.Pattern -> File
      getPattern (A.VarP x)    = bound x
      getPattern (A.AsP _ x _) = bound x
      getPattern (A.DotP pi _) =
        singleton (P.getRange pi)
                  (mempty { otherAspects = [DottedPattern] })
      getPattern _             = mempty

      getFieldDecl :: A.Declaration -> File
      getFieldDecl (A.RecDef _ _ _ _ _ fs) = Fold.foldMap extractField fs
        where
        extractField (A.ScopedDecl _ ds) = Fold.foldMap extractField ds
        extractField (A.Field _ x _)     = field (concreteQualifier x)
                                                 (concreteBase x)
        extractField _                   = mempty
      getFieldDecl _                   = mempty

      getModuleName :: A.ModuleName -> File
      getModuleName m@(A.MName { A.mnameToList = xs }) =
        mconcat $ map (mod isTopLevelModule) xs
        where
        isTopLevelModule =
          case catMaybes $
               map (join .
                    fmap P.srcFile .
                    P.rStart .
                    A.nameBindingSite) xs of
            f : _ -> Map.lookup f modMap ==
                     Just (C.toTopLevelModuleName $ A.mnameToConcrete m)
            []    -> False

      getModuleInfo :: SI.ModuleInfo -> File
      getModuleInfo (SI.ModuleInfo { SI.minfoAsTo   = asTo
                                   , SI.minfoAsName = name }) =
        aToF Symbol asTo `mappend` maybe mempty asName name

-- | A function mapping names to the kind of name they stand for.

type NameKinds = A.QName -> Maybe NameKind

-- | Builds a 'NameKinds' function.

nameKinds :: Maybe TCErr  -- ^ 'Nothing' if type checking completed
                          --   successfully.
          -> [A.Declaration]
          -> TCM NameKinds
nameKinds mErr decls = do
  imported <- fix . stImports <$> get
  local    <- case mErr of
    Nothing -> fix . stSignature <$> get
    Just _  -> return $
      -- Traverses the syntax tree and constructs a map from qualified
      -- names to name kinds. TODO: Handle open public.
      everything' union (Map.empty `mkQ` getDecl) decls
  let merged = Map.union local imported
  return (\n -> Map.lookup n merged)
  where
  fix = HMap.map (defnToNameKind . theDef) . sigDefinitions

  -- | The 'M.Axiom' constructor is used to represent various things
  -- which are not really axioms, so when maps are merged 'Postulate's
  -- are thrown away whenever possible. The 'getDef' and 'getDecl'
  -- functions below can return several explanations for one qualified
  -- name; the 'Postulate's are bogus.
  union = HMap.unionWith dropPostulates
    where
      dropPostulates Postulate k = k
      dropPostulates k         _ = k

  defnToNameKind :: Defn -> NameKind
  defnToNameKind (M.Axiom {})                     = Postulate
  defnToNameKind (M.Function {})                  = Function
  defnToNameKind (M.Datatype {})                  = Datatype
  defnToNameKind (M.Record {})                    = Record
  defnToNameKind (M.Constructor { M.conInd = i }) = Constructor i
  defnToNameKind (M.Primitive {})                 = Primitive

  getAxiomName :: A.Declaration -> A.QName
  getAxiomName (A.Axiom _ _ q _) = q
  getAxiomName _                 = __IMPOSSIBLE__

  getDecl :: A.Declaration -> HashMap A.QName NameKind
  getDecl (A.Axiom _ _ q _)   = HMap.singleton q Postulate
  getDecl (A.Field _ q _)     = HMap.singleton q Function
    -- Note that the name q can be used both as a field name and as a
    -- projection function. Highlighting of field names is taken care
    -- of by "theRest" above, which does not use NameKinds.
  getDecl (A.Primitive _ q _) = HMap.singleton q Primitive
  getDecl (A.Mutual {})       = HMap.empty
  getDecl (A.Section {})      = HMap.empty
  getDecl (A.Apply {})        = HMap.empty
  getDecl (A.Import {})       = HMap.empty
  getDecl (A.Pragma {})       = HMap.empty
  getDecl (A.ScopedDecl {})   = HMap.empty
  getDecl (A.Open {})         = HMap.empty
  getDecl (A.FunDef  _ q _)       = HMap.singleton q Function
  getDecl (A.DataSig _ q _ _)       = HMap.singleton q Datatype
  getDecl (A.DataDef _ q _ cs)    = HMap.singleton q Datatype `union`
                                   (HMap.unions $
                                    map (\q -> HMap.singleton q (Constructor SC.Inductive)) $
                                    map getAxiomName cs)
  getDecl (A.RecSig _ q _ _)      = HMap.singleton q Record
  getDecl (A.RecDef _ q c _ _ _)  = HMap.singleton q Record `union`
                                   case c of
                                     Nothing -> HMap.empty
                                     Just q ->
                                       HMap.singleton q (Constructor SC.Inductive)

-- | Generates syntax highlighting information for all constructors
-- occurring in patterns and expressions in the given declarations.
--
-- This function should only be called after type checking.
-- Constructors can be overloaded, and the overloading is resolved by
-- the type checker.

generateConstructorInfo
  :: SourceToModule  -- ^ Maps source file paths to module names.
  -> AbsolutePath    -- ^ The module to highlight.
  -> NameKinds
  -> [A.Declaration]
  -> TCM File
generateConstructorInfo modMap file kinds decls = do
  -- Extract all defined names from the declaration list.
  let names = Fold.toList $ Fold.foldMap A.allNames decls

  -- Look up the corresponding declarations in the internal syntax.
  defMap <- M.sigDefinitions <$> M.getSignature
  let defs = catMaybes $ map (flip HMap.lookup defMap) names

  -- Instantiate meta variables.
  clauses <- R.instantiateFull $ concatMap M.defClauses defs
  types   <- R.instantiateFull $ map defType defs

  -- Find all constructors occurring in type signatures or clauses
  -- within the given declarations.
  constrs <- getConstrs (types, clauses)

  -- Return suitable syntax highlighting information.
  return $ Fold.fold $ fmap (generate modMap file kinds . mkAmb) constrs
  where
  mkAmb q = A.AmbQ [q]

  getConstrs :: (UniverseBi a I.Pattern, UniverseBi a I.Term) =>
                a -> TCM [A.QName]
  getConstrs x = do
    termConstrs <- concat <$> mapM getConstructor (universeBi x)
    return (patternConstrs ++ termConstrs)
    where
    patternConstrs = concatMap getConstructorP (universeBi x)

  getConstructorP :: I.Pattern -> [A.QName]
  getConstructorP (I.ConP q _ _) = [q]
  getConstructorP _              = []

  getConstructor :: I.Term -> TCM [A.QName]
  getConstructor (I.Con q _) = return [q]
  getConstructor (I.Def c _)
    | fmap P.srcFile (P.rStart (P.getRange c)) == Just (Just file)
                             = retrieveCoconstructor c
  getConstructor _           = return []

  retrieveCoconstructor :: A.QName -> TCM [A.QName]
  retrieveCoconstructor c = do
    def <- getConstInfo c
    case defDelayed def of
      -- Not a coconstructor.
      NotDelayed -> return []

      Delayed -> do
        clauses <- R.instantiateFull $ defClauses def
        case clauses of
          [I.Clause{ I.clauseBody = body }] -> case getRHS body of
            Just (I.Con c args) -> (c :) <$> getConstrs args

            -- The meta variable could not be instantiated.
            Just (I.MetaV {})   -> return []

            _                   -> __IMPOSSIBLE__

          _ -> __IMPOSSIBLE__
    where
      getRHS (I.Body v)   = Just v
      getRHS I.NoBody     = Nothing
      getRHS (I.Bind b)   = getRHS (I.unAbs b)

-- | Generates syntax highlighting information for unsolved meta
-- variables.

computeUnsolvedMetaWarnings :: TCM File
computeUnsolvedMetaWarnings = do
  is <- getInteractionMetas

  -- We don't want to highlight blocked terms, since
  --   * there is always at least one proper meta responsible for the blocking
  --   * in many cases the blocked term covers the highlighting for this meta
  let notBlocked m = not <$> isBlockedTerm m
  ms <- filterM notBlocked =<< getOpenMetas

  rs <- mapM getMetaRange (ms \\ is)
  return $ several (map P.continuousPerLine rs)
                   (mempty { otherAspects = [UnsolvedMeta] })

-- | Generates syntax highlighting information for unsolved constraints
-- that are not connected to a meta variable.

computeUnsolvedConstraints :: TCM File
computeUnsolvedConstraints = do
  cs <- getAllConstraints
  -- get ranges of emptyness constraints
  let rs = [ r | PConstr{ theConstraint = Closure{ clValue = IsEmpty r t }} <- cs ]
  return $ several (map P.continuousPerLine rs)
                   (mempty { otherAspects = [UnsolvedConstraint] })

-- | Generates a suitable file for a possibly ambiguous name.

generate :: SourceToModule
            -- ^ Maps source file paths to module names.
         -> AbsolutePath
            -- ^ The module to highlight.
         -> NameKinds
         -> A.AmbiguousQName
         -> File
generate modMap file kinds (A.AmbQ qs) =
  mconcat $ map (\q -> nameToFileA modMap file q include m) qs
  where
    ks   = map kinds qs
    kind = case (allEqual ks, ks) of
             (True, Just k : _) -> Just k
             _                  -> Nothing
    -- Note that all names in an AmbiguousQName should have the same
    -- concrete name, so either they are all operators, or none of
    -- them are.
    m isOp  = mempty { aspect = Just $ Name kind isOp }
    include = allEqual (map bindingSite qs)

-- | Converts names to suitable 'File's.

nameToFile :: SourceToModule
              -- ^ Maps source file paths to module names.
           -> AbsolutePath
              -- ^ The file name of the current module. Used for
              -- consistency checking.
           -> [C.Name]
              -- ^ The name qualifier (may be empty).
           -> C.Name
              -- ^ The base name.
           -> (Bool -> MetaInfo)
              -- ^ Meta information to be associated with the name.
              -- The argument is 'True' iff the name is an operator.
           -> Maybe P.Range
              -- ^ The definition site of the name. The calculated
              -- meta information is extended with this information,
              -- if possible.
           -> File
nameToFile modMap file xs x m mR =
  -- We don't care if we get any funny ranges.
  if all (== Just file) fileNames then
    several rs ((m $ C.isOperator x) { definitionSite = mFilePos })
   else
    mempty
  where
  fileNames  = catMaybes $ map (fmap P.srcFile . P.rStart . P.getRange) (x : xs)
  rs         = map P.getRange (x : xs)
  mFilePos   = do
    r <- mR
    P.Pn { P.srcFile = Just f, P.posPos = p } <- P.rStart r
    mod <- Map.lookup f modMap
    return (mod, toInteger p)

-- | A variant of 'nameToFile' for qualified abstract names.

nameToFileA :: SourceToModule
               -- ^ Maps source file paths to module names.
            -> AbsolutePath
               -- ^ The file name of the current module. Used for
               -- consistency checking.
            -> A.QName
               -- ^ The name.
            -> Bool
               -- ^ Should the binding site be included in the file?
            -> (Bool -> MetaInfo)
               -- ^ Meta information to be associated with the name.
               -- ^ The argument is 'True' iff the name is an operator.
            -> File
nameToFileA modMap file x include m =
  nameToFile modMap
             file
             (concreteQualifier x)
             (concreteBase x)
             m
             (if include then Just $ bindingSite x else Nothing)

concreteBase      = A.nameConcrete . A.qnameName
concreteQualifier = map A.nameConcrete . A.mnameToList . A.qnameModule
bindingSite       = A.nameBindingSite . A.qnameName

------------------------------------------------------------------------
-- All tests

-- | All the properties.

tests :: IO Bool
tests = runTests "Agda.Interaction.Highlighting.Generate" []
