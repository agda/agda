{-# LANGUAGE CPP, FlexibleContexts, RelaxedPolyRec #-}

-- | Generates data used for precise syntax highlighting.

module Agda.Interaction.Highlighting.Generate
  ( Level(..)
  , generateAndPrintSyntaxInfo
  , generateTokenInfo
  , printErrorInfo
  , printUnsolvedInfo
  , printHighlightingInfo
  , highlightAsTypeChecked
  , Agda.Interaction.Highlighting.Generate.tests
  ) where

import Agda.Interaction.FindFile
import Agda.Interaction.Response (Response(Resp_HighlightingInfo))
import Agda.Interaction.Highlighting.Emacs   hiding (tests)
import Agda.Interaction.Highlighting.Precise hiding (tests)
import Agda.Interaction.Highlighting.Range   hiding (tests)
import Agda.Interaction.EmacsCommand
import qualified Agda.TypeChecking.Errors as E
import Agda.TypeChecking.MetaVars (isBlockedTerm)
import Agda.TypeChecking.Monad.Options (reportSLn, reportSDoc)
import Agda.TypeChecking.Monad
  hiding (MetaInfo, Primitive, Constructor, Record, Function, Datatype)
import qualified Agda.TypeChecking.Monad as M
import Agda.TypeChecking.Pretty
import qualified Agda.TypeChecking.Reduce as R
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Common (Delayed(..))
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
import Control.Arrow ((***))
import Data.Monoid
import Data.Function
import Data.Generics.Geniplate
import Agda.Utils.FileName
import qualified Agda.Utils.IO.UTF8 as UTF8
import Agda.Utils.Monad
import Data.HashSet (HashSet)
import qualified Data.HashSet as HSet
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.List ((\\), isPrefixOf)
import qualified Data.Foldable as Fold (toList, fold, foldMap)
import System.Directory
import System.IO

import Agda.Utils.Impossible
#include "../../undefined.h"

-- | @highlightAsTypeChecked rPre r m@ runs @m@ and returns its
-- result. Some code may additionally be highlighted:
--
-- * If @r@ is non-empty and not a sub-range of @rPre@ (after
--   'P.continuousPerLine' has been applied to both): @r@ is
--   highlighted as being type-checked while @m@ is running (this
--   highlighting is removed if @m@ completes /successfully/).
--
-- * Otherwise: Highlighting is removed for @rPre - r@ before @m@
--   runs, and if @m@ completes successfully, then @rPre - r@ is
--   highlighted as being type-checked.

highlightAsTypeChecked
  :: MonadTCM tcm
  => P.Range
  -> P.Range
  -> tcm a
  -> tcm a
highlightAsTypeChecked rPre r m
  | r /= P.noRange && delta == rPre' = wrap r'    highlight clear
  | otherwise                        = wrap delta clear     highlight
  where
  rPre'     = rToR (P.continuousPerLine rPre)
  r'        = rToR (P.continuousPerLine r)
  delta     = rPre' `minus` r'
  clear     = mempty
  highlight = mempty { otherAspects = [TypeChecks] }

  wrap rs x y = do
    p rs x
    v <- m
    p rs y
    return v
    where
    p rs x = printHighlightingInfo (singletonC rs x)

-- | Lispify and print the given highlighting information.

printHighlightingInfo :: MonadTCM tcm => HighlightingInfo -> tcm ()
printHighlightingInfo x = do
  liftTCM $ reportSLn "highlighting" 50 $
    "Printing highlighting info:\n" ++ show x
  unless (null $ ranges x) $ do
    st <- get
    liftTCM $ appInteractionOutputCallback $
        Resp_HighlightingInfo x (stModuleToSource st)

-- | Highlighting levels.

data Level
  = Full [TerminationError]
    -- ^ Full highlighting. Should only be used after typechecking has
    -- completed successfully.
    --
    -- The list of termination problems is also highlighted.
    --
    -- Precondition: The termination problems must be located in the
    -- module that is highlighted.
  | Partial
    -- ^ Highlighting without disambiguation of overloaded
    -- constructors.

-- | Generate syntax highlighting information for the given
-- declaration, and (if appropriate) print it. If the
-- 'HighlightingLevel' is @'Full' something@, then the state is
-- additionally updated with the new highlighting info (in case of a
-- conflict new info takes precedence over old info).
--
-- The procedure makes use of some of the token highlighting info in
-- 'stTokens' (that corresponding to the interval covered by the
-- declaration). If the 'HighlightingLevel' is @'Full' something@,
-- then this token highlighting info is additionally removed from
-- 'stTokens'.

generateAndPrintSyntaxInfo :: A.Declaration -> Level -> TCM ()
generateAndPrintSyntaxInfo decl hlLevel = do
  file <- envCurrentPath <$> ask

  reportSLn "import.iface.create" 15 $
      "Generating syntax info for " ++ filePath file ++ ' ' :
        case hlLevel of
            Full    {} -> "(final)"
            Partial {} -> "(first approximation)"
        ++ "."

  M.ignoreAbstractMode $ do
    modMap <- sourceToModule
    kinds  <- nameKinds hlLevel decl

    let nameInfo = mconcat $ map (generate modMap file kinds) names

    -- Constructors are only highlighted after type checking, since they
    -- can be overloaded.
    constructorInfo <- case hlLevel of
      Full _ -> generateConstructorInfo modMap file kinds decl
      _      -> return mempty

    let (from, to) = case P.rangeToInterval (P.getRange decl) of
          Nothing -> __IMPOSSIBLE__
          Just i  -> let conv = toInteger . P.posPos in
                     (conv $ P.iStart i, conv $ P.iEnd i)
    (prevTokens, (curTokens, postTokens)) <-
      (id *** splitAtC to) . splitAtC from . stTokens <$> get

    -- theRest needs to be placed before nameInfo here since record
    -- field declarations contain QNames. constructorInfo also needs
    -- to be placed before nameInfo since, when typechecking is done,
    -- constructors are included in both lists. Finally the token
    -- information is placed last since token highlighting is more
    -- crude than the others.
    let syntaxInfo = compress (mconcat [ constructorInfo
                                       , theRest modMap file
                                       , nameInfo
                                       , termInfo
                                       ])
                       `mappend`
                     curTokens

    case hlLevel of
      Full _ -> modify (\st ->
                  st { stSyntaxInfo = syntaxInfo `mappend` stSyntaxInfo st
                     , stTokens     = prevTokens `mappend` postTokens
                     })
      _      -> return ()

    ifTopLevelAndHighlightingLevelIs NonInteractive $
      printHighlightingInfo syntaxInfo
  where
  -- Highlighting of termination problems.
  termInfo = case hlLevel of
    Full termErrs -> functionDefs `mappend` callSites
      where
      m            = mempty { otherAspects = [TerminationProblem] }
      functionDefs = Fold.foldMap (\x -> singleton (rToR $ bindingSite x) m) $
                     concatMap M.termErrFunctions termErrs
      callSites    = Fold.foldMap (\r -> singleton (rToR r) m) $
                     concatMap (map M.callInfoRange . M.termErrCalls) termErrs
    _ -> mempty

  -- All names mentioned in the syntax tree (not bound variables).
  names :: [A.AmbiguousQName]
  names =
    (map (A.AmbQ . (:[])) $
     filter (not . extendedLambda) $
     universeBi decl) ++
    universeBi decl
    where
    extendedLambda :: A.QName -> Bool
    extendedLambda n = extendlambdaname `isPrefixOf` show (A.qnameName n)

  -- Bound variables, dotted patterns, record fields, module names,
  -- the "as" and "to" symbols.
  theRest modMap file = mconcat
    [ Fold.foldMap getFieldDecl   $ universeBi decl
    , Fold.foldMap getVarAndField $ universeBi decl
    , Fold.foldMap getLet         $ universeBi decl
    , Fold.foldMap getLam         $ universeBi decl
    , Fold.foldMap getTyped       $ universeBi decl
    , Fold.foldMap getPattern     $ universeBi decl
    , Fold.foldMap getModuleName  $ universeBi decl
    , Fold.foldMap getModuleInfo  $ universeBi decl
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
    getLet A.LetPatBind{}        = mempty
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
      singleton (rToR $ P.getRange pi)
                (mempty { otherAspects = [DottedPattern] })
    getPattern _             = mempty

    getFieldDecl :: A.Declaration -> File
    getFieldDecl (A.RecDef _ _ _ _ _ _ fs) = Fold.foldMap extractField fs
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
      singleton (rToR asTo) (mempty { aspect = Just Symbol })
        `mappend`
      maybe mempty asName name

-- | Generate and return the syntax highlighting information for the
-- tokens in the given file.

generateTokenInfo
  :: AbsolutePath          -- ^ The module to highlight.
  -> TCM CompressedFile
generateTokenInfo file = do
  tokens <- liftIO $ Pa.parseFile' Pa.tokensParser file
  return $ merge $ map tokenToCFile tokens
  where
  -- Converts an aspect and a range to a file.
  aToF a r = singletonC (rToR r) (mempty { aspect = Just a })

  -- Merges /sorted, non-overlapping/ compressed files.
  merge = CompressedFile . concat . map ranges

  tokenToCFile :: T.Token -> CompressedFile
  tokenToCFile (T.TokSetN (i, _))               = aToF PrimitiveType (P.getRange i)
  tokenToCFile (T.TokKeyword T.KwSet  i)        = aToF PrimitiveType (P.getRange i)
  tokenToCFile (T.TokKeyword T.KwProp i)        = aToF PrimitiveType (P.getRange i)
  tokenToCFile (T.TokKeyword T.KwForall i)      = aToF Symbol (P.getRange i)
  tokenToCFile (T.TokKeyword _ i)               = aToF Keyword (P.getRange i)
  tokenToCFile (T.TokSymbol  _ i)               = aToF Symbol (P.getRange i)
  tokenToCFile (T.TokLiteral (L.LitInt    r _)) = aToF Number r
  tokenToCFile (T.TokLiteral (L.LitFloat  r _)) = aToF Number r
  tokenToCFile (T.TokLiteral (L.LitString r _)) = aToF String r
  tokenToCFile (T.TokLiteral (L.LitChar   r _)) = aToF String r
  tokenToCFile (T.TokLiteral (L.LitQName  r _)) = aToF String r
  tokenToCFile (T.TokComment (i, _))            = aToF Comment (P.getRange i)
  tokenToCFile (T.TokTeX (i, _))                = aToF Comment (P.getRange i)
  tokenToCFile (T.TokId {})                     = mempty
  tokenToCFile (T.TokQId {})                    = mempty
  tokenToCFile (T.TokString {})                 = mempty
  tokenToCFile (T.TokDummy {})                  = mempty
  tokenToCFile (T.TokEOF {})                    = mempty

-- | A function mapping names to the kind of name they stand for.

type NameKinds = A.QName -> Maybe NameKind

-- | Builds a 'NameKinds' function.

nameKinds :: Level
             -- ^ This should only be @'Full' something@ if
             -- type-checking completed successfully (without any
             -- errors).
          -> A.Declaration
          -> TCM NameKinds
nameKinds hlLevel decl = do
  imported <- fix . stImports <$> get
  local    <- case hlLevel of
    Full _ -> fix . stSignature <$> get
    _      -> return $
      -- Traverses the syntax tree and constructs a map from qualified
      -- names to name kinds. TODO: Handle open public.
      foldr ($) HMap.empty $ map declToKind $ universeBi decl
  let merged = HMap.union local imported
  return (\n -> HMap.lookup n merged)
  where
  fix = HMap.map (defnToKind . theDef) . sigDefinitions

  -- | The 'M.Axiom' constructor is used to represent various things
  -- which are not really axioms, so when maps are merged 'Postulate's
  -- are thrown away whenever possible. The 'declToKind' function
  -- below can return several explanations for one qualified name; the
  -- 'Postulate's are bogus.
  insert = HMap.insertWith dropPostulates
    where
    dropPostulates Postulate k = k
    dropPostulates k         _ = k

  defnToKind :: Defn -> NameKind
  defnToKind (M.Axiom {})                     = Postulate
  defnToKind (M.Function {})                  = Function
  defnToKind (M.Datatype {})                  = Datatype
  defnToKind (M.Record {})                    = Record
  defnToKind (M.Constructor { M.conInd = i }) = Constructor i
  defnToKind (M.Primitive {})                 = Primitive

  getAxiomName :: A.Declaration -> A.QName
  getAxiomName (A.Axiom _ _ q _) = q
  getAxiomName _                 = __IMPOSSIBLE__

  declToKind :: A.Declaration ->
                HashMap A.QName NameKind -> HashMap A.QName NameKind
  declToKind (A.Axiom _ _ q _)      = insert q Postulate
  declToKind (A.Field _ q _)        = insert q Function
    -- Note that the name q can be used both as a field name and as a
    -- projection function. Highlighting of field names is taken care
    -- of by "theRest" above, which does not use NameKinds.
  declToKind (A.Primitive _ q _)    = insert q Primitive
  declToKind (A.Mutual {})          = id
  declToKind (A.Section {})         = id
  declToKind (A.Apply {})           = id
  declToKind (A.Import {})          = id
  declToKind (A.Pragma {})          = id
  declToKind (A.ScopedDecl {})      = id
  declToKind (A.Open {})            = id
  declToKind (A.FunDef  _ q _ _)    = insert q Function
  declToKind (A.DataSig _ q _ _)    = insert q Datatype
  declToKind (A.DataDef _ q _ cs)   = \m ->
                                      insert q Datatype $
                                      foldr (\d -> insert (getAxiomName d)
                                                          (Constructor SC.Inductive))
                                            m cs
  declToKind (A.RecSig _ q _ _)     = insert q Record
  declToKind (A.RecDef _ q _ c _ _ _) = insert q Record .
                                      case c of
                                        Nothing -> id
                                        Just q  -> insert q (Constructor SC.Inductive)

-- | Generates syntax highlighting information for all constructors
-- occurring in patterns and expressions in the given declaration.
--
-- This function should only be called after type checking.
-- Constructors can be overloaded, and the overloading is resolved by
-- the type checker.

generateConstructorInfo
  :: SourceToModule  -- ^ Maps source file paths to module names.
  -> AbsolutePath    -- ^ The module to highlight.
  -> NameKinds
  -> A.Declaration
  -> TCM File
generateConstructorInfo modMap file kinds decl = do
  -- Extract all defined names from the declaration.
  let names = Fold.toList (A.allNames decl)

  -- Look up the corresponding declarations in the internal syntax.
  defMap <- M.sigDefinitions <$> M.getSignature
  let defs = catMaybes $ map (flip HMap.lookup defMap) names

  -- Instantiate meta variables.
  clauses <- R.instantiateFull $ concatMap M.defClauses defs
  types   <- R.instantiateFull $ map defType defs

  let -- Find all patterns and terms.
      patterns = universeBi (types, clauses)
      terms    = universeBi (types, clauses)

      -- Find all constructors in the patterns and terms.
      constrs = concatMap getConstructorP patterns ++
                concatMap getConstructor  terms

  -- Find all constructors in right-hand sides of delayed definitions.
  delayed <- evalStateT (getDelayed terms) HSet.empty

  -- Return suitable syntax highlighting information.
  return $ Fold.fold $ fmap (generate modMap file kinds . mkAmb)
                            (delayed ++ constrs)
  where
  mkAmb q = A.AmbQ [q]

  -- Finds names corresponding to delayed definitions occurring at the
  -- top of the given terms, as well as in the found definition's
  -- right-hand sides. Only definitions from the current file are
  -- considered.
  --
  -- Constructors occurring in the delayed definitions' right-hand
  -- sides are returned.
  --
  -- The set is used to avoid inspecting the same definition multiple
  -- times.

  getDelayed :: [I.Term] -> StateT (HashSet A.QName) TCM [A.QName]
  getDelayed ts = concat <$> mapM getT ts
    where
    getT t = do
      lift $ reportSDoc "highlighting.delayed" 50 $
        text "Inspecting sub-term:" <+> prettyTCM t

      seen <- get
      case t of
        I.Def q _ | not (q `HSet.member` seen)
                      &&
                    fmap P.srcFile (P.rStart (P.getRange q)) ==
                      Just (Just file)
                  -> getQ q
        _         -> return []

    getQ q = do
      lift $ reportSDoc "highlighting.delayed" 30 $
        text "Inspecting name:" <+> prettyTCM q

      def <- lift $ getConstInfo q
      case defDelayed def of
        NotDelayed -> return []
        Delayed    -> do
          lift $ reportSDoc "highlighting.delayed" 10 $
            text "Found delayed definition:" <+> prettyTCM q

          -- Mark the definition as seen.
          modify (HSet.insert q)

          -- All sub-terms in the delayed definition's right-hand
          -- sides.
          terms <- universeBi . concat . map (getRHS . I.clauseBody) <$>
                     lift (R.instantiateFull $ defClauses def)

          -- Find the constructors and continue the search.
          (concatMap getConstructor terms ++) <$> getDelayed terms

    getRHS (I.Body v)   = [v]
    getRHS I.NoBody     = []
    getRHS (I.Bind b)   = getRHS (I.unAbs b)

  getConstructorP :: I.Pattern -> [A.QName]
  getConstructorP (I.ConP q _ _) = [q]
  getConstructorP _              = []

  getConstructor :: I.Term -> [A.QName]
  getConstructor (I.Con q _) = [q]
  getConstructor _           = []

-- | Prints syntax highlighting info for an error.

printErrorInfo :: TCErr -> TCM ()
printErrorInfo e = do
  file <- envCurrentPath <$> ask
  let r = P.getRange e
  case P.rStart r of
    Just x | P.srcFile x == Just file -> do
      s <- E.prettyError e

      -- Erase previous highlighting.
      p (P.continuousPerLine r) mempty

      -- Print new highlighting.
      p r $ mempty { otherAspects = [Error]
                   , note         = Just s
                   }
    _ -> internalError . ("invalid range when printing error: " ++) =<< E.prettyError e
  where
  p r x = printHighlightingInfo $ singletonC (rToR r) x

-- | Generates and prints syntax highlighting information for unsolved
-- meta-variables and certain unsolved constraints.

printUnsolvedInfo :: TCM ()
printUnsolvedInfo = do
  metaInfo       <- computeUnsolvedMetaWarnings
  constraintInfo <- computeUnsolvedConstraints

  printHighlightingInfo
    (compress $ metaInfo `mappend` constraintInfo)

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
  return $ several (map (rToR . P.continuousPerLine) rs)
                   (mempty { otherAspects = [UnsolvedMeta] })

-- | Generates syntax highlighting information for unsolved constraints
-- that are not connected to a meta variable.

computeUnsolvedConstraints :: TCM File
computeUnsolvedConstraints = do
  cs <- getAllConstraints
  -- get ranges of emptyness constraints
  let rs = [ r | PConstr{ theConstraint = Closure{ clValue = IsEmpty r t }} <- cs ]
  return $ several (map (rToR . P.continuousPerLine) rs)
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
    several (map rToR rs)
            ((m $ C.isOperator x) { definitionSite = mFilePos })
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
