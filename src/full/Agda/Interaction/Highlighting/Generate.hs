{-# LANGUAGE CPP, Rank2Types, RelaxedPolyRec #-}

-- | Generates data used for precise syntax highlighting.

module Agda.Interaction.Highlighting.Generate
  ( generateSyntaxInfo
  , generateErrorInfo
  , highlightAsTypeChecked
  , Agda.Interaction.Highlighting.Generate.tests
  )
  where

import Agda.Interaction.FindFile
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
import Control.Monad
import Control.Monad.Trans
import Control.Monad.State
import Control.Applicative
import Data.Monoid
import Data.Function
import Agda.Utils.Generics
import Agda.Utils.FileName
import qualified Agda.Utils.IO.UTF8 as UTF8
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Sequence (Seq, (><))
import Data.List ((\\), isPrefixOf)
import qualified Data.Sequence as Seq
import qualified Data.Foldable as Fold (toList, fold, foldMap)
import System.Directory
import System.IO

import Agda.Utils.Impossible
#include "../../undefined.h"

-- | Highlights the given thing as having been type-checked.
--
-- TODO: Only for the current module, etc.

highlightAsTypeChecked :: (P.HasRange r, MonadTCM tcm) => r -> tcm ()
highlightAsTypeChecked x
  | null file = return ()
  | otherwise = liftIO $ do
      dir    <- getTemporaryDirectory
      (f, h) <- openTempFile dir "agda"
      UTF8.hPutStr h $
        showHighlightingInfo $ Just (file, __IMPOSSIBLE__)
      hClose h
      putResponse $
        L [A "agda2-highlight-load", A (show f), Q (A "keep")]
  where
  file = compress $
         several (rToR $ P.getRange x) $
         mempty { otherAspects = [TypeChecked] }

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
  several (rToR $ P.continuousPerLine r)
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
    let nameInfo = mconcat $ map (generate modMap file kinds)
                                 (Fold.toList names)
    -- Constructors are only highlighted after type checking, since they
    -- can be overloaded.
    constructorInfo <- case mErr of
      Nothing -> generateConstructorInfo modMap file kinds decls
      Just _  -> return mempty
    metaInfo <- case mErr of
      Nothing -> computeUnsolvedMetaWarnings
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
      , termInfo
      , tokInfo tokens
      ]
  where
    decls = CA.topLevelDecls top

    -- Converts an aspect and a range to a file.
    aToF a r = several (rToR r) (mempty { aspect = Just a })

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
      functionDefs = Fold.foldMap (\x -> several (rToR $ bindingSite x) m) $
                     concatMap M.termErrFunctions termErrs
      callSites    = Fold.foldMap (\r -> several (rToR r) m) $
                     concatMap (map M.callInfoRange . M.termErrCalls) termErrs

    -- All names mentioned in the syntax tree (not bound variables).
    names = everything' (><) (Seq.empty `mkQ`  getName
                                        `extQ` getAmbiguous)
                        decls
      where
      getName :: A.QName -> Seq A.AmbiguousQName
      getName n | isPrefixOf extendlambdaname $ show $ A.qnameName n = mempty
                | otherwise                                          = Seq.singleton (A.AmbQ [n])


      getAmbiguous :: A.AmbiguousQName -> Seq A.AmbiguousQName
      getAmbiguous = Seq.singleton

    -- Bound variables, dotted patterns, record fields, module names,
    -- the "as" and "to" symbols.
    theRest modMap = everything' mappend query decls
      where
      query :: GenericQ File
      query = mempty         `mkQ`
              getFieldDecl   `extQ`
              getVarAndField `extQ`
              getLet         `extQ`
              getLam         `extQ`
              getTyped       `extQ`
              getPattern     `extQ`
              getModuleName  `extQ`
              getModuleInfo

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
        several (rToR $ P.getRange pi)
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
  fix = Map.map (defnToNameKind . theDef) . sigDefinitions

  -- | The 'M.Axiom' constructor is used to represent various things
  -- which are not really axioms, so when maps are merged 'Postulate's
  -- are thrown away whenever possible. The 'getDef' and 'getDecl'
  -- functions below can return several explanations for one qualified
  -- name; the 'Postulate's are bogus.
  union = Map.unionWith dropPostulates
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

  getDecl :: A.Declaration -> Map A.QName NameKind
  getDecl (A.Axiom _ _ q _)   = Map.singleton q Postulate
  getDecl (A.Field _ q _)     = Map.singleton q Function
    -- Note that the name q can be used both as a field name and as a
    -- projection function. Highlighting of field names is taken care
    -- of by "theRest" above, which does not use NameKinds.
  getDecl (A.Primitive _ q _) = Map.singleton q Primitive
  getDecl (A.Mutual {})       = Map.empty
  getDecl (A.Section {})      = Map.empty
  getDecl (A.Apply {})        = Map.empty
  getDecl (A.Import {})       = Map.empty
  getDecl (A.Pragma {})       = Map.empty
  getDecl (A.ScopedDecl {})   = Map.empty
  getDecl (A.Open {})         = Map.empty
  getDecl (A.FunDef  _ q _)       = Map.singleton q Function
  getDecl (A.DataSig _ q _ _)       = Map.singleton q Datatype
  getDecl (A.DataDef _ q _ cs)    = Map.singleton q Datatype `union`
                                   (Map.unions $
                                    map (\q -> Map.singleton q (Constructor SC.Inductive)) $
                                    map getAxiomName cs)
  getDecl (A.RecSig _ q _ _)      = Map.singleton q Record
  getDecl (A.RecDef _ q c _ _ _)  = Map.singleton q Record `union`
                                   case c of
                                     Nothing -> Map.empty
                                     Just q ->
                                       Map.singleton q (Constructor SC.Inductive)

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
  let defs = catMaybes $ map (flip Map.lookup defMap) names

  -- Instantiate meta variables.
  clauses <- R.instantiateFull $ concatMap M.defClauses defs
  types   <- R.instantiateFull $ map defType defs

  -- Find all constructors occurring in type signatures or clauses
  -- within the given declarations.
  constrs <- everything' (liftM2 (><)) query (types, clauses)

  -- Return suitable syntax highlighting information.
  return $ Fold.fold $ fmap (generate modMap file kinds . mkAmb) constrs
  where
  mkAmb q = A.AmbQ [q]

  query :: GenericQ (TCM (Seq A.QName))
  query = return mempty   `mkQ`
          getConstructor  `extQ`
          getConstructorP

  getConstructor :: I.Term -> TCM (Seq A.QName)
  getConstructor (I.Con q _) = return $ Seq.singleton q
  getConstructor (I.Def c _)
    | fmap P.srcFile (P.rStart (P.getRange c)) == Just (Just file)
                             = retrieveCoconstructor c
  getConstructor _           = return Seq.empty

  getConstructorP :: I.Pattern -> TCM (Seq A.QName)
  getConstructorP (I.ConP q _ _) = return $ Seq.singleton q
  getConstructorP _              = return Seq.empty

  retrieveCoconstructor :: A.QName -> TCM (Seq A.QName)
  retrieveCoconstructor c = do
    def <- getConstInfo c
    case defDelayed def of
      -- Not a coconstructor.
      NotDelayed -> return Seq.empty

      Delayed -> do
        clauses <- R.instantiateFull $ defClauses def
        case clauses of
          [I.Clause{ I.clauseBody = body }] -> case getRHS body of
            Just (I.Con c args) -> do
              s <- everything' (liftM2 (><)) query args
              return $ Seq.singleton c >< s

            -- The meta variable could not be instantiated.
            Just (I.MetaV {})   -> return Seq.empty

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
  return $ several (concatMap (rToR . P.continuousPerLine) rs)
         $ mempty { otherAspects = [UnsolvedMeta] }

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
    several rs' ((m isOp) { definitionSite = mFilePos })
   else
    mempty
  where
  fileNames  = catMaybes $ map (fmap P.srcFile . P.rStart . P.getRange) (x : xs)
  (rs, isOp) = getRanges x
  rs'        = rs ++ concatMap (fst . getRanges) xs
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

-- | Like 'everything', but modified so that it does not descend into
-- everything.

everything' :: (r -> r -> r) -> GenericQ r -> GenericQ r
everything' (+) = everythingBut
                    (+)
                    (False `mkQ` isString
                           `extQ` isAQName `extQ` isAName `extQ` isCName
                           `extQ` isScope `extQ` isMap1 `extQ` isMap2
                           `extQ` isAmbiguous)
  where
  isString    :: String                        -> Bool
  isAQName    :: A.QName                       -> Bool
  isAName     :: A.Name                        -> Bool
  isCName     :: C.Name                        -> Bool
  isScope     :: S.ScopeInfo                   -> Bool
  isMap1      :: Map A.QName A.QName           -> Bool
  isMap2      :: Map A.ModuleName A.ModuleName -> Bool
  isAmbiguous :: A.AmbiguousQName              -> Bool

  isString    = const True
  isAQName    = const True
  isAName     = const True
  isCName     = const True
  isScope     = const True
  isMap1      = const True
  isMap2      = const True
  isAmbiguous = const True

------------------------------------------------------------------------
-- All tests

-- | All the properties.

tests :: IO Bool
tests = runTests "Agda.Interaction.Highlighting.Generate" []
