{-# LANGUAGE CPP              #-}

-- | Generates data used for precise syntax highlighting.

module Agda.Interaction.Highlighting.Generate
  ( Level(..)
  , generateAndPrintSyntaxInfo
  , generateTokenInfo, generateTokenInfoFromSource
  , generateTokenInfoFromString
  , printSyntaxInfo
  , printErrorInfo, errorHighlighting
  , printUnsolvedInfo
  , printHighlightingInfo
  , highlightAsTypeChecked
  , warningHighlighting
  , computeUnsolvedMetaWarnings
  , computeUnsolvedConstraints
  , storeDisambiguatedName, disambiguateRecordFields
  ) where

import Prelude hiding (null)

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Reader
import Control.Arrow (second)

import Data.Monoid
import Data.Generics.Geniplate
import qualified Data.Map as Map
import Data.Maybe
import Data.List ((\\), isPrefixOf)
import qualified Data.List as List
import qualified Data.Foldable as Fold (fold, foldMap, toList)
import qualified Data.IntMap as IntMap
import qualified Data.Text.Lazy as T
import Data.Void

import Agda.Interaction.Response (Response(Resp_HighlightingInfo))
import Agda.Interaction.Highlighting.Precise
import Agda.Interaction.Highlighting.Range
import Agda.Interaction.Response
  (RemoveTokenBasedHighlighting(KeepHighlighting))

import qualified Agda.TypeChecking.Errors as E
import Agda.TypeChecking.MetaVars (isBlockedTerm)
import Agda.TypeChecking.Monad
  hiding (MetaInfo, Primitive, Constructor, Record, Function, Datatype)
import qualified Agda.TypeChecking.Monad as M
import Agda.TypeChecking.Positivity.Occurrence
import Agda.TypeChecking.Warnings (runPM)

import Agda.Syntax.Abstract (IsProjP(..))
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Concrete (FieldAssignment'(..))
import Agda.Syntax.Concrete.Definitions ( DeclarationWarning(..) )
import qualified Agda.Syntax.Common as Common
import qualified Agda.Syntax.Concrete.Name as C
import qualified Agda.Syntax.Concrete as C
import Agda.Syntax.Fixity
import qualified Agda.Syntax.Info as SI
import qualified Agda.Syntax.Internal as I
import qualified Agda.Syntax.Literal as L
import qualified Agda.Syntax.Parser as Pa
import qualified Agda.Syntax.Parser.Tokens as T
import qualified Agda.Syntax.Position as P
import Agda.Syntax.Position (getRange)

import Agda.Utils.FileName
import Agda.Utils.Function
import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.Maybe
import qualified Agda.Utils.Maybe.Strict as Strict
import Agda.Utils.Null
import Agda.Utils.Pretty
import Agda.Utils.HashMap (HashMap)
import qualified Agda.Utils.HashMap as HMap

#include "undefined.h"
import Agda.Utils.Impossible

-- | @highlightAsTypeChecked rPre r m@ runs @m@ and returns its
--   result. Additionally, some code may be highlighted:
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
  highlight = parserBased { otherAspects = [TypeChecks] }

  wrap rs x y = do
    p rs x
    v <- m
    p rs y
    return v
    where
    p rs x = printHighlightingInfo KeepHighlighting (singletonC rs x)

-- | Lispify and print the given highlighting information.

printHighlightingInfo ::
  MonadTCM tcm =>
  RemoveTokenBasedHighlighting ->
  HighlightingInfo ->
  tcm ()
printHighlightingInfo remove info = do
  modToSrc <- useTC stModuleToSource
  method   <- viewTC eHighlightingMethod
  liftTCM $ reportSLn "highlighting" 50 $ unlines
    [ "Printing highlighting info:"
    , show info
    , "  modToSrc = " ++ show modToSrc
    ]
  unless (null $ ranges info) $ do
    liftTCM $ appInteractionOutputCallback $
        Resp_HighlightingInfo info remove method modToSrc

-- | Highlighting levels.

data Level
  = Full
    -- ^ Full highlighting. Should only be used after typechecking has
    --   completed successfully.
  | Partial
    -- ^ Highlighting without disambiguation of overloaded
    --   constructors.

-- | Generate syntax highlighting information for the given
-- declaration, and (if appropriate) print it. If the boolean is
-- 'True', then the state is additionally updated with the new
-- highlighting info (in case of a conflict new info takes precedence
-- over old info).
--
-- The procedure makes use of some of the token highlighting info in
-- 'stTokens' (that corresponding to the interval covered by the
-- declaration). If the boolean is 'True', then this token
-- highlighting info is additionally removed from 'stTokens'.

generateAndPrintSyntaxInfo
  :: A.Declaration
  -> Level
  -> Bool
     -- ^ Update the state?
  -> TCM ()
generateAndPrintSyntaxInfo decl _ _ | null $ P.getRange decl = return ()
generateAndPrintSyntaxInfo decl hlLevel updateState = do
  file <- getCurrentPath

  reportSLn "import.iface.create" 15 $
      "Generating syntax info for " ++ filePath file ++ ' ' :
        case hlLevel of
            Full    {} -> "(final)"
            Partial {} -> "(first approximation)"
        ++ "."

  reportSLn "highlighting.names" 60 $ "highlighting names = " ++ prettyShow names

  M.ignoreAbstractMode $ do
    modMap <- sourceToModule
    kinds  <- nameKinds hlLevel decl

    let nameInfo = mconcat $ map (generate modMap file kinds) names

    -- Constructors are only highlighted after type checking, since they
    -- can be overloaded.
    constructorInfo <- case hlLevel of
      Full{} -> generateConstructorInfo modMap file kinds decl
      _      -> return mempty

    cm <- P.rangeFile <$> viewTC eRange
    reportSLn "highlighting.warning" 60 $ "current path = " ++ show cm

    warnInfo <- Fold.foldMap warningHighlighting
                 . filter ((cm ==) . tcWarningOrigin) <$> useTC stTCWarnings

    let (from, to) = case P.rangeToInterval (P.getRange decl) of
          Nothing -> __IMPOSSIBLE__
          Just i  -> ( fromIntegral $ P.posPos $ P.iStart i
                     , fromIntegral $ P.posPos $ P.iEnd i)
    (prevTokens, (curTokens, postTokens)) <-
      second (splitAtC to) . splitAtC from <$> useTC stTokens

    -- theRest needs to be placed before nameInfo here since record
    -- field declarations contain QNames. constructorInfo also needs
    -- to be placed before nameInfo since, when typechecking is done,
    -- constructors are included in both lists. Finally the token
    -- information is placed last since token highlighting is more
    -- crude than the others.
    let syntaxInfo = compress (mconcat [ constructorInfo
                                       , theRest modMap file
                                       , nameInfo
                                       , warnInfo
                                       ])
                       `mappend`
                     curTokens

    when updateState $ do
      stSyntaxInfo `modifyTCLens` mappend syntaxInfo
      stTokens     `setTCLens` (prevTokens `mappend` postTokens)

    ifTopLevelAndHighlightingLevelIs NonInteractive $
      printHighlightingInfo KeepHighlighting syntaxInfo
  where
  -- All names mentioned in the syntax tree (not bound variables).
  names :: [A.AmbiguousQName]
  names =
    (map I.unambiguous $
     filter (not . isExtendedLambdaName) $
     universeBi decl) ++
    universeBi decl

  -- Bound variables, dotted patterns, record fields, module names,
  -- the "as" and "to" symbols.
  theRest modMap file = mconcat
    [ Fold.foldMap getFieldDecl   $ universeBi decl
    , Fold.foldMap getVarAndField $ universeBi decl
    , Fold.foldMap getLet         $ universeBi decl
    , Fold.foldMap getLam         $ universeBi decl
    , Fold.foldMap getTyped       $ universeBi decl
    , Fold.foldMap getPattern     $ universeBi decl
    , Fold.foldMap getPatternSyn  $ universeBi decl
    , Fold.foldMap getExpr        $ universeBi decl
    , Fold.foldMap getPatSynArgs  $ universeBi decl
    , Fold.foldMap getModuleName  $ universeBi decl
    , Fold.foldMap getModuleInfo  $ universeBi decl
    , Fold.foldMap getNamedArg    $ universeBi decl
    ]
    where
    bound (A.BindName n) =
      nameToFile modMap file [] (A.nameConcrete n) P.noRange
                 (\isOp -> parserBased { aspect =
                             Just $ Name (Just Bound) isOp })
                 (Just $ A.nameBindingSite n)

    patsyn n =               -- TODO: resolve overloading
              nameToFileA modMap file (I.headAmbQ n) True $ \isOp ->
                  parserBased { aspect =
                    Just $ Name (Just $ Constructor Common.Inductive) isOp }

    macro n = nameToFileA modMap file n True $ \isOp ->
                  parserBased { aspect = Just $ Name (Just Macro) isOp }

    field :: [C.Name] -> C.Name -> File
    field m n = nameToFile modMap file m n P.noRange
                           (\isOp -> parserBased { aspect =
                                       Just $ Name (Just Field) isOp })
                           Nothing
    asName n = nameToFile modMap file []
                          n P.noRange
                          (\isOp -> parserBased { aspect =
                                      Just $ Name (Just Module) isOp })
                          Nothing

    -- For top level modules, we set the binding site to the beginning of the file
    -- so that clicking on an imported module will jump to the beginning of the file
    -- which defines this module.
    mod isTopLevelModule n =
      nameToFile modMap file []
                 (A.nameConcrete n) P.noRange
                 (\isOp -> parserBased { aspect =
                             Just $ Name (Just Module) isOp })
                 (Just $ applyWhen isTopLevelModule P.beginningOfFile $
                           A.nameBindingSite n)

    getVarAndField :: A.Expr -> File
    getVarAndField (A.Var x)            = bound $ A.BindName x
    -- Andreas, 2018-06-09, issue #3120
    -- The highlighting for record field tags is now created by the type checker in
    -- function disambiguateRecordFields.
    -- Andreas, Nisse, 2018-10-26, issue #3322
    -- Still, we extract the highlighting info here for uses such as QuickLatex.
    -- The aspects from the disambiguation will be merged in.
    getVarAndField (A.Rec       _ fs)   = mconcat [ field [] x | Left (FieldAssignment x _) <- fs ]
    getVarAndField (A.RecUpdate _ _ fs) = mconcat [ field [] x |      (FieldAssignment x _) <- fs ]
    getVarAndField _                    = mempty

    -- Ulf, 2014-04-09: It would be nicer to have it on Named_ a, but
    -- you can't have polymorphic functions in universeBi.
    getNamedArg :: Common.RString -> File
    getNamedArg x = singleton (rToR $ P.getRange x) $
                       parserBased { aspect =
                         Just $ Name (Just Argument) False }

    getLet :: A.LetBinding -> File
    getLet (A.LetBind _ _ x _ _)     = bound x
    getLet A.LetPatBind{}            = mempty
    getLet A.LetApply{}              = mempty
    getLet A.LetOpen{}               = mempty
    getLet (A.LetDeclaredVariable x) = bound x

    getLam :: A.LamBinding -> File
    getLam (A.DomainFree x)  = bound $ Common.namedArg x
    getLam (A.DomainFull {}) = mempty

    getTyped :: A.TypedBinding -> File
    getTyped (A.TBind _ xs _) = mconcat $ map (bound . Common.namedArg) xs
    getTyped A.TLet{}         = mempty

    getPatSynArgs :: A.Declaration -> File
    getPatSynArgs (A.PatternSynDef _ xs _) = mconcat $ map (bound . A.BindName . Common.unArg) xs
    getPatSynArgs _                        = mempty

    getPattern' :: IsProjP e => A.Pattern' e -> File
    getPattern' (A.VarP x)    = bound x
    getPattern' (A.AsP _ x _) = bound x
    getPattern' (A.DotP pi e)
      | Just _ <- isProjP e = mempty
      | otherwise =
          singleton (rToR $ P.getRange pi)
                (parserBased { otherAspects = [DottedPattern] })
    getPattern' (A.PatternSynP _ q _) = patsyn q
    -- Andreas, 2018-06-09, issue #3120
    -- The highlighting for record field tags is now created by the type checker in
    -- function disambiguateRecordFields.
    -- Andreas, Nisse, 2018-10-26, issue #3322
    -- Still, we extract the highlighting info here for uses such as QuickLatex.
    -- The aspects from the disambiguation will be merged in.
    getPattern' (A.RecP _ fs) = mconcat [ field [] x | FieldAssignment x _ <- fs ]
    getPattern' _             = mempty

    getPattern :: A.Pattern -> File
    getPattern = getPattern'

    getPatternSyn :: A.Pattern' Void -> File
    getPatternSyn = getPattern'

    getExpr :: A.Expr -> File
    getExpr (A.PatternSyn q) = patsyn q
    getExpr (A.Macro q)      = macro q
    getExpr _                = mempty

    getFieldDecl :: A.Declaration -> File
    getFieldDecl (A.RecDef _ _ _ _ _ _ _ _ fs) = Fold.foldMap extractField fs
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
        case mapMaybe (join .
                  fmap (Strict.toLazy . P.srcFile) .
                  P.rStart .
                  A.nameBindingSite) xs of
          f : _ -> Map.lookup f modMap ==
                   Just (C.toTopLevelModuleName $ A.mnameToConcrete m)
          []    -> False

    getModuleInfo :: SI.ModuleInfo -> File
    getModuleInfo (SI.ModuleInfo { SI.minfoAsTo   = asTo
                                 , SI.minfoAsName = name }) =
      singleton (rToR asTo) (parserBased { aspect = Just Symbol })
        `mappend`
      maybe mempty asName name

-- | Generate and return the syntax highlighting information for the
-- tokens in the given file.

generateTokenInfo :: AbsolutePath -> TCM CompressedFile
generateTokenInfo file =
  generateTokenInfoFromSource file . T.unpack =<<
    runPM (Pa.readFilePM file)

-- | Generate and return the syntax highlighting information for the
-- tokens in the given file.

generateTokenInfoFromSource
  :: AbsolutePath
     -- ^ The module to highlight.
  -> String
     -- ^ The file contents. Note that the file is /not/ read from
     -- disk.
  -> TCM CompressedFile
generateTokenInfoFromSource file input =
  runPM $ tokenHighlighting <$> fst <$> Pa.parseFile Pa.tokensParser file input

-- | Generate and return the syntax highlighting information for the
-- tokens in the given string, which is assumed to correspond to the
-- given range.

generateTokenInfoFromString :: P.Range -> String -> TCM CompressedFile
generateTokenInfoFromString r _ | r == P.noRange = return mempty
generateTokenInfoFromString r s = do
  runPM $ tokenHighlighting <$> Pa.parsePosString Pa.tokensParser p s
  where
    Just p = P.rStart r

-- | Compute syntax highlighting for the given tokens.
tokenHighlighting :: [T.Token] -> CompressedFile
tokenHighlighting = merge . map tokenToCFile
  where
  -- Converts an aspect and a range to a file.
  aToF a r = singletonC (rToR r) (mempty { aspect = Just a })

  -- Merges /sorted, non-overlapping/ compressed files.
  merge = CompressedFile . concat . map ranges

  tokenToCFile :: T.Token -> CompressedFile
  tokenToCFile (T.TokSetN (i, _))               = aToF PrimitiveType (P.getRange i)
  tokenToCFile (T.TokPropN (i, _))              = aToF PrimitiveType (P.getRange i)
  tokenToCFile (T.TokKeyword T.KwSet  i)        = aToF PrimitiveType (P.getRange i)
  tokenToCFile (T.TokKeyword T.KwProp i)        = aToF PrimitiveType (P.getRange i)
  tokenToCFile (T.TokKeyword T.KwForall i)      = aToF Symbol (P.getRange i)
  tokenToCFile (T.TokKeyword _ i)               = aToF Keyword (P.getRange i)
  tokenToCFile (T.TokSymbol  _ i)               = aToF Symbol (P.getRange i)
  tokenToCFile (T.TokLiteral (L.LitNat    r _)) = aToF Number r
  tokenToCFile (T.TokLiteral (L.LitWord64 r _)) = aToF Number r
  tokenToCFile (T.TokLiteral (L.LitFloat  r _)) = aToF Number r
  tokenToCFile (T.TokLiteral (L.LitString r _)) = aToF String r
  tokenToCFile (T.TokLiteral (L.LitChar   r _)) = aToF String r
  tokenToCFile (T.TokLiteral (L.LitQName  r _)) = aToF String r
  tokenToCFile (T.TokLiteral (L.LitMeta r _ _)) = aToF String r
  tokenToCFile (T.TokComment (i, _))            = aToF Comment (P.getRange i)
  tokenToCFile (T.TokTeX (i, _))                = aToF Background (P.getRange i)
  tokenToCFile (T.TokMarkup (i, _))             = aToF Markup (P.getRange i)
  tokenToCFile (T.TokId {})                     = mempty
  tokenToCFile (T.TokQId {})                    = mempty
  tokenToCFile (T.TokString (i,s))              = aToF Pragma (P.getRange i)
  tokenToCFile (T.TokDummy {})                  = mempty
  tokenToCFile (T.TokEOF {})                    = mempty

-- | A function mapping names to the kind of name they stand for.

type NameKinds = A.QName -> Maybe NameKind

-- | Builds a 'NameKinds' function.

nameKinds :: Level
             -- ^ This should only be @'Full'@ if
             -- type-checking completed successfully (without any
             -- errors).
          -> A.Declaration
          -> TCM NameKinds
nameKinds hlLevel decl = do
  imported <- fix <$> useTC stImports
  local    <- case hlLevel of
    Full{} -> fix <$> useTC stSignature
    _      -> return HMap.empty
      -- Traverses the syntax tree and constructs a map from qualified
      -- names to name kinds. TODO: Handle open public.
  let syntax = foldr ($) HMap.empty $ map declToKind $ universeBi decl
  let merged = unions [local, imported, syntax]
  return (\n -> HMap.lookup n merged)
  where
  fix = HMap.map (defnToKind . theDef) . (^. sigDefinitions)

  -- | The 'M.Axiom' constructor is used to represent various things
  -- which are not really axioms, so when maps are merged 'Postulate's
  -- are thrown away whenever possible. The 'declToKind' function
  -- below can return several explanations for one qualified name; the
  -- 'Postulate's are bogus.
  merge Postulate k = k
  merge _     Macro = Macro  -- If the abstract syntax says macro, it's a macro.
  merge k         _ = k

  unions = foldr (HMap.unionWith merge) HMap.empty
  insert = HMap.insertWith merge

  defnToKind :: Defn -> NameKind
  defnToKind   M.Axiom{}                           = Postulate
  defnToKind   M.DataOrRecSig{}                    = Postulate
  defnToKind   M.GeneralizableVar{}                = Bound    -- TODO: separate kind for generalizable vars
  defnToKind d@M.Function{} | isProperProjection d = Field
                            | otherwise            = Function
  defnToKind   M.Datatype{}                        = Datatype
  defnToKind   M.Record{}                          = Record
  defnToKind   M.Constructor{ M.conInd = i }       = Constructor i
  defnToKind   M.Primitive{}                       = Primitive
  defnToKind   M.AbstractDefn{}                    = __IMPOSSIBLE__

  declToKind :: A.Declaration ->
                HashMap A.QName NameKind -> HashMap A.QName NameKind
  declToKind (A.Axiom _ i _ _ q _)
    | SI.defMacro i == Common.MacroDef = insert q Macro
    | otherwise                        = insert q Postulate
  declToKind (A.Field _ q _)        = insert q Field -- Function
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
  declToKind (A.PatternSynDef q _ _) = insert q (Constructor Common.Inductive)
  declToKind (A.Generalize _ _ _ q _)  = insert q Postulate
  declToKind (A.FunDef  _ q _ _)     = insert q Function
  declToKind (A.UnquoteDecl _ _ qs _) = foldr (\ q f -> insert q Function . f) id qs
  declToKind (A.UnquoteDef _ qs _)    = foldr (\ q f -> insert q Function . f) id qs
  declToKind (A.DataSig _ q _ _)      = insert q Datatype
  declToKind (A.DataDef _ q _ _ cs)   = \m ->
                                      insert q Datatype $
                                      foldr (\d -> insert (A.axiomName d)
                                                          (Constructor Common.Inductive))
                                            m cs
  declToKind (A.RecSig _ q _ _)       = insert q Record
  declToKind (A.RecDef _ q _ _ _ c _ _ _) = insert q Record .
                                      case c of
                                        Nothing -> id
                                        Just q  -> insert q (Constructor Common.Inductive)

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

  -- Get boundaries of current declaration.
  -- @noRange@ should be impossible, but in case of @noRange@
  -- it makes sense to return the empty File.
  ifNull (P.rangeIntervals $ P.getRange decl)
         (return mempty) $ \is -> do
    let start = fromIntegral $ P.posPos $ P.iStart $ head is
        end   = fromIntegral $ P.posPos $ P.iEnd   $ last is

    -- Get all disambiguated names that fall within the range of decl.
    m0 <- useTC stDisambiguatedNames
    let (_, m1) = IntMap.split (pred start) m0
        (m2, _) = IntMap.split end m1
        constrs = IntMap.elems m2

    -- Return suitable syntax highlighting information.
    let files = for constrs $ \ q -> generate modMap file kinds $ I.unambiguous q
    return $ Fold.fold files

printSyntaxInfo :: P.Range -> TCM ()
printSyntaxInfo r = do
  syntaxInfo <- useTC stSyntaxInfo
  ifTopLevelAndHighlightingLevelIs NonInteractive $
      printHighlightingInfo KeepHighlighting (selectC r syntaxInfo)

-- | Prints syntax highlighting info for an error.

printErrorInfo :: TCErr -> TCM ()
printErrorInfo e =
  printHighlightingInfo KeepHighlighting . compress =<<
    errorHighlighting e

-- | Generate highlighting for error.
--   Does something special for termination errors.

errorHighlighting :: TCErr -> TCM File
errorHighlighting e = do

  -- Erase previous highlighting.
  let r     = P.getRange e
      erase = singleton (rToR $ P.continuousPerLine r) mempty

  -- Print new highlighting.
  s <- E.prettyError e
  let error = singleton (rToR r)
         $ parserBased { otherAspects = [Error]
                       , note         = Just s
                       }
  return $ mconcat [ erase, error ]

-- | Generate syntax highlighting for warnings.

warningHighlighting :: TCWarning -> File
warningHighlighting w = case tcWarning w of
  TerminationIssue terrs     -> terminationErrorHighlighting terrs
  NotStrictlyPositive d ocs  -> positivityErrorHighlighting d ocs
  UnreachableClauses{}       -> deadcodeHighlighting $ P.getRange w
  CoverageIssue{}            -> coverageErrorHighlighting $ P.getRange w
  CoverageNoExactSplit{}     -> catchallHighlighting $ P.getRange w
  UnsolvedConstraints cs     -> constraintsHighlighting cs
  UnsolvedMetaVariables rs   -> metasHighlighting rs
  AbsurdPatternRequiresNoRHS{} -> deadcodeHighlighting $ P.getRange w
  ModuleDoesntExport{}         -> deadcodeHighlighting $ P.getRange w
  -- expanded catch-all case to get a warning for new constructors
  CantGeneralizeOverSorts{}  -> mempty
  UnsolvedInteractionMetas{} -> mempty
  OldBuiltin{}               -> mempty
  EmptyRewritePragma{}       -> deadcodeHighlighting $ P.getRange w
  IllformedAsClause{}        -> deadcodeHighlighting $ P.getRange w
  UselessPublic{}            -> mempty
  UselessInline{}            -> mempty
  InstanceWithExplicitArg{}  -> deadcodeHighlighting $ P.getRange w
  ParseWarning{}             -> mempty
  InversionDepthReached{}    -> mempty
  GenericWarning{}           -> mempty
  GenericNonFatalError{}     -> mempty
  SafeFlagPostulate{}        -> mempty
  SafeFlagPragma{}           -> mempty
  SafeFlagNonTerminating     -> mempty
  SafeFlagTerminating        -> mempty
  SafeFlagWithoutKFlagPrimEraseEquality -> mempty
  WithoutKFlagPrimEraseEquality -> mempty
  SafeFlagNoPositivityCheck  -> mempty
  SafeFlagPolarity           -> mempty
  SafeFlagNoUniverseCheck    -> mempty
  DeprecationWarning{}       -> mempty
  UserWarning{}              -> mempty
  LibraryWarning{}           -> mempty
  InfectiveImport{}          -> mempty
  CoInfectiveImport{}        -> mempty
  NicifierIssue w           -> case w of
    -- we intentionally override the binding of `w` here so that our pattern of
    -- using `P.getRange w` still yields the most precise range information we
    -- can get.
    NotAllowedInMutual{} -> deadcodeHighlighting $ P.getRange w
    EmptyAbstract{}      -> deadcodeHighlighting $ P.getRange w
    EmptyInstance{}      -> deadcodeHighlighting $ P.getRange w
    EmptyMacro{}         -> deadcodeHighlighting $ P.getRange w
    EmptyMutual{}        -> deadcodeHighlighting $ P.getRange w
    EmptyPostulate{}     -> deadcodeHighlighting $ P.getRange w
    EmptyPrivate{}       -> deadcodeHighlighting $ P.getRange w
    EmptyGeneralize{}    -> deadcodeHighlighting $ P.getRange w
    UselessAbstract{}    -> deadcodeHighlighting $ P.getRange w
    UselessInstance{}    -> deadcodeHighlighting $ P.getRange w
    UselessPrivate{}     -> deadcodeHighlighting $ P.getRange w
    _ -> mempty -- TODO: explore highlighting opportunities here!



-- | Generate syntax highlighting for termination errors.

terminationErrorHighlighting :: [TerminationError] -> File
terminationErrorHighlighting termErrs = functionDefs `mappend` callSites
  where
    m            = parserBased { otherAspects = [TerminationProblem] }
    functionDefs = Fold.foldMap (\x -> singleton (rToR $ bindingSite x) m) $
                   concatMap M.termErrFunctions termErrs
    callSites    = Fold.foldMap (\r -> singleton (rToR r) m) $
                   concatMap (map M.callInfoRange . M.termErrCalls) termErrs

-- | Generate syntax highlighting for not-strictly-positive inductive
-- definitions.

-- TODO: highlight also the problematic occurrences
positivityErrorHighlighting :: I.QName -> OccursWhere -> File
positivityErrorHighlighting q o = several (rToR <$> P.getRange q : rs) m
  where
    rs = case o of Unknown -> []; Known r _ -> [r]
    m  = parserBased { otherAspects = [PositivityProblem] }

deadcodeHighlighting :: P.Range -> File
deadcodeHighlighting r = singleton (rToR $ P.continuousPerLine r) m
  where m = parserBased { otherAspects = [Deadcode] }

coverageErrorHighlighting :: P.Range -> File
coverageErrorHighlighting r = singleton (rToR $ P.continuousPerLine r) m
  where m = parserBased { otherAspects = [CoverageProblem] }


catchallHighlighting :: P.Range -> File
catchallHighlighting r = singleton (rToR $ P.continuousPerLine r) m
  where m = parserBased { otherAspects = [CatchallClause] }


-- | Generates and prints syntax highlighting information for unsolved
-- meta-variables and certain unsolved constraints.

printUnsolvedInfo :: TCM ()
printUnsolvedInfo = do
  metaInfo       <- computeUnsolvedMetaWarnings
  constraintInfo <- computeUnsolvedConstraints

  printHighlightingInfo KeepHighlighting
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
  return $ metasHighlighting rs

metasHighlighting :: [P.Range] -> File
metasHighlighting rs = several (map (rToR . P.continuousPerLine) rs)
                     $ parserBased { otherAspects = [UnsolvedMeta] }

-- | Generates syntax highlighting information for unsolved constraints
--   (ideally: that are not connected to a meta variable).

computeUnsolvedConstraints :: TCM File
computeUnsolvedConstraints = constraintsHighlighting <$> getAllConstraints

constraintsHighlighting :: Constraints -> File
constraintsHighlighting cs =
  several (map (rToR . P.continuousPerLine) rs)
          (parserBased { otherAspects = [UnsolvedConstraint] })
  where
  -- get ranges of interesting unsolved constraints
  rs = (`mapMaybe` (map theConstraint cs)) $ \case
    Closure{ clValue = IsEmpty r t           } -> Just r
    Closure{ clEnv = e, clValue = ValueCmp{} } -> Just $ getRange (envRange e)
    Closure{ clEnv = e, clValue = ElimCmp{}  } -> Just $ getRange (envRange e)
    Closure{ clEnv = e, clValue = TypeCmp{}  } -> Just $ getRange (envRange e)
    Closure{ clEnv = e, clValue = TelCmp{}   } -> Just $ getRange (envRange e)
    Closure{ clEnv = e, clValue = SortCmp{}  } -> Just $ getRange (envRange e)
    Closure{ clEnv = e, clValue = LevelCmp{} } -> Just $ getRange (envRange e)
    Closure{ clEnv = e, clValue = CheckSizeLtSat{} } -> Just $ getRange (envRange e)
    _ -> Nothing

-- | Generates a suitable file for a possibly ambiguous name.

generate :: SourceToModule
            -- ^ Maps source file paths to module names.
         -> AbsolutePath
            -- ^ The module to highlight.
         -> NameKinds
         -> A.AmbiguousQName
         -> File
generate modMap file kinds (A.AmbQ qs) =
  Fold.foldMap (\ q -> nameToFileA modMap file q include m) qs
  where
    ks   = map kinds (Fold.toList qs)
    -- Ulf, 2014-06-03: [issue1064] It's better to pick the first rather
    -- than doing no highlighting if there's an ambiguity between an
    -- inductive and coinductive constructor.
    kind = case [ k | Just k <- ks ] of
             k : _ -> Just k
             []    -> Nothing
    -- kind = case (allEqual ks, ks) of
    --          (True, Just k : _) -> Just k
    --          _                  -> Nothing
    -- Note that all names in an AmbiguousQName should have the same
    -- concrete name, so either they are all operators, or none of
    -- them are.
    m isOp  = parserBased { aspect = Just $ Name kind isOp }
    include = allEqual (map bindingSite $ Fold.toList qs)

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
           -> P.Range
              -- ^ The 'Range' of the name in its fixity declaration (if any).
           -> (Bool -> Aspects)
              -- ^ Meta information to be associated with the name.
              -- The argument is 'True' iff the name is an operator.
           -> Maybe P.Range
              -- ^ The definition site of the name. The calculated
              -- meta information is extended with this information,
              -- if possible.
           -> File
nameToFile modMap file xs x fr m mR =
  -- We don't care if we get any funny ranges.
  if all (== Strict.Just file) fileNames then
    frFile `mappend`
    several (map rToR rs)
            (aspects { definitionSite = mFilePos })
   else
    mempty
  where
  aspects    = m $ C.isOperator x
  fileNames  = mapMaybe (fmap P.srcFile . P.rStart . P.getRange) (x : xs)
  frFile     = singleton (rToR fr) (aspects { definitionSite = notHere <$> mFilePos })
  rs         = map P.getRange (x : xs)

  -- The fixity declaration should not get a symbolic anchor.
  notHere d = d { defSiteHere = False }

  mFilePos  :: Maybe DefinitionSite
  mFilePos   = do
    r <- mR
    P.Pn { P.srcFile = Strict.Just f, P.posPos = p } <- P.rStart r
    mod <- Map.lookup f modMap
    -- Andreas, 2017-06-16, Issue #2604: Symbolic anchors.
    -- We drop the file name part from the qualifiers, since
    -- this is contained in the html file name already.
    -- We want to get anchors of the form:
    -- @<a name="TopLevelModule.html#LocalModule.NestedModule.identifier">@
    let qualifiers = drop (length $ C.moduleNameParts mod) xs
    -- For bound variables, we do not create symbolic anchors.
        local = maybe True isLocalAspect $ aspect aspects
    return $ DefinitionSite
      { defSiteModule = mod
      , defSitePos    = fromIntegral p
        -- Is our current position the definition site?
      , defSiteHere   = r == P.getRange x
        -- For bound variables etc. we do not create a symbolic anchor name.
        -- Also not for names that include anonymous modules,
        -- otherwise, we do not get unique anchors.
      , defSiteAnchor = if local || C.isNoName x || any Common.isUnderscore qualifiers
          then Nothing
          else Just $ prettyShow $ foldr C.Qual (C.QName x) qualifiers
      }

  -- Is the name a bound variable or similar? If in doubt, yes.
  isLocalAspect :: Aspect -> Bool
  isLocalAspect = \case
    Name mkind _ -> maybe True isLocal mkind
    _ -> True
  isLocal :: NameKind -> Bool
  isLocal = \case
    Bound         -> True
    Argument      -> True
    Constructor{} -> False
    Datatype      -> False
    Field         -> False
    Function      -> False
    Module        -> False
    Postulate     -> False
    Primitive     -> False
    Record        -> False
    Macro         -> False


-- | A variant of 'nameToFile' for qualified abstract names.

nameToFileA
  :: SourceToModule
     -- ^ Maps source file paths to module names.
  -> AbsolutePath
     -- ^ The file name of the current module. Used for
     -- consistency checking.
  -> A.QName
     -- ^ The name.
  -> Bool
     -- ^ Should the binding site be included in the file?
  -> (Bool -> Aspects)
     -- ^ Meta information to be associated with the name.
     -- ^ The argument is 'True' iff the name is an operator.
  -> File
nameToFileA modMap file x include m =
  nameToFile modMap
             file
             (concreteQualifier x)
             (concreteBase x)
             r
             m
             (if include then Just $ bindingSite x else Nothing)
  where
    -- Andreas, 2016-09-08, for issue #2140:
    -- Range of name from fixity declaration:
    fr = theNameRange $ A.nameFixity $ A.qnameName x
    -- Somehow we import fixity ranges from other files, we should ignore them.
    -- (I do not understand how we get them as they should not be serialized...)
    r = if P.rangeFile fr == Strict.Just file then fr else P.noRange

concreteBase :: I.QName -> C.Name
concreteBase = A.nameConcrete . A.qnameName

concreteQualifier :: I.QName -> [C.Name]
concreteQualifier = map A.nameConcrete . A.mnameToList . A.qnameModule

bindingSite :: I.QName -> P.Range
bindingSite = A.nameBindingSite . A.qnameName

-- | Remember a name disambiguation (during type checking).
--   To be used later during syntax highlighting.
storeDisambiguatedName :: A.QName -> TCM ()
storeDisambiguatedName q = whenJust (start $ P.getRange q) $ \ i ->
  stDisambiguatedNames `modifyTCLens` IntMap.insert i q
  where
  start r = fromIntegral . P.posPos <$> P.rStart' r

-- | Store a disambiguation of record field tags for the purpose of highlighting.
disambiguateRecordFields
  :: [C.Name]   -- ^ Record field names in a record expression.
  -> [A.QName]  -- ^ Record field names in the corresponding record type definition
  -> TCM ()
disambiguateRecordFields cxs axs = forM_ cxs $ \ cx -> do
  caseMaybe (List.find ((cx ==) . A.nameConcrete . A.qnameName) axs) (return ()) $ \ ax -> do
    storeDisambiguatedName ax { A.qnameName = (A.qnameName ax) { A.nameConcrete = cx } }
