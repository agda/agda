{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RelaxedPolyRec #-}

-- | Generates data used for precise syntax highlighting.

module Agda.Interaction.Highlighting.Generate
  ( Level(..)
  , generateAndPrintSyntaxInfo
  , generateTokenInfo, generateTokenInfoFromString
  , printSyntaxInfo
  , printErrorInfo, errorHighlighting
  , printUnsolvedInfo
  , printHighlightingInfo
  , highlightAsTypeChecked
  , computeUnsolvedMetaWarnings
  , computeUnsolvedConstraints
  , storeDisambiguatedName
  , Agda.Interaction.Highlighting.Generate.tests
  ) where

import Prelude hiding (null)

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Reader
import Control.Applicative
import Control.Arrow (second)

import Data.Monoid
import Data.Generics.Geniplate
import qualified Data.Map as Map
import Data.Maybe
import Data.List ((\\), isPrefixOf)
import qualified Data.Foldable as Fold (fold, foldMap)
import qualified Data.IntMap as IntMap

import Agda.Interaction.Response (Response(Resp_HighlightingInfo))
import Agda.Interaction.Highlighting.Precise hiding (tests)
import Agda.Interaction.Highlighting.Range   hiding (tests)

import qualified Agda.TypeChecking.Errors as E
import Agda.TypeChecking.MetaVars (isBlockedTerm)
import Agda.TypeChecking.Monad
  hiding (MetaInfo, Primitive, Constructor, Record, Function, Datatype)
import qualified Agda.TypeChecking.Monad as M

import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Concrete (FieldAssignment'(..))
import qualified Agda.Syntax.Common as Common
import qualified Agda.Syntax.Concrete as C
import qualified Agda.Syntax.Info as SI
import qualified Agda.Syntax.Internal as I
import qualified Agda.Syntax.Literal as L
import qualified Agda.Syntax.Parser as Pa
import qualified Agda.Syntax.Parser.Tokens as T
import qualified Agda.Syntax.Position as P

import Agda.Utils.FileName
import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Null
import Agda.Utils.TestHelpers
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
  modToSrc <- use stModuleToSource
  liftTCM $ reportSLn "highlighting" 50 $
    "Printing highlighting info:\n" ++ show x ++ "\n" ++
    "  modToSrc = " ++ show modToSrc
  unless (null $ ranges x) $ do
    liftTCM $ appInteractionOutputCallback $
        Resp_HighlightingInfo x modToSrc

-- | Highlighting levels.

data Level
  = Full
    -- ^ Full highlighting. Should only be used after typechecking has
    --   completed successfully.
  | Partial
    -- ^ Highlighting without disambiguation of overloaded
    --   constructors.

-- | Generate syntax highlighting information for the given
-- declaration, and (if appropriate) print it. If the
-- 'HighlightingLevel' is @'Full'@, then the state is
-- additionally updated with the new highlighting info (in case of a
-- conflict new info takes precedence over old info).
--
-- The procedure makes use of some of the token highlighting info in
-- 'stTokens' (that corresponding to the interval covered by the
-- declaration). If the 'HighlightingLevel' is @'Full'@,
-- then this token highlighting info is additionally removed from
-- 'stTokens'.

generateAndPrintSyntaxInfo :: A.Declaration -> Level -> TCM ()
generateAndPrintSyntaxInfo decl _ | null $ P.getRange decl = return ()
generateAndPrintSyntaxInfo decl hlLevel = do
  file <- fromMaybe __IMPOSSIBLE__ <$> asks envCurrentPath

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
      Full{} -> generateConstructorInfo modMap file kinds decl
      _      -> return mempty

    let (from, to) = case P.rangeToInterval (P.getRange decl) of
          Nothing -> __IMPOSSIBLE__
          Just i  -> ( fromIntegral $ P.posPos $ P.iStart i
                     , fromIntegral $ P.posPos $ P.iEnd i)
    (prevTokens, (curTokens, postTokens)) <-
      (second (splitAtC to)) . splitAtC from <$> use stTokens

    -- theRest needs to be placed before nameInfo here since record
    -- field declarations contain QNames. constructorInfo also needs
    -- to be placed before nameInfo since, when typechecking is done,
    -- constructors are included in both lists. Finally the token
    -- information is placed last since token highlighting is more
    -- crude than the others.
    let syntaxInfo = compress (mconcat [ constructorInfo
                                       , theRest modMap file
                                       , nameInfo
                                       ])
                       `mappend`
                     curTokens

    case hlLevel of
      Full{} -> do stSyntaxInfo %= mappend syntaxInfo
                   stTokens     .= prevTokens `mappend` postTokens
      _      -> return ()

    ifTopLevelAndHighlightingLevelIs NonInteractive $
      printHighlightingInfo syntaxInfo
  where
  -- All names mentioned in the syntax tree (not bound variables).
  names :: [A.AmbiguousQName]
  names =
    (map (A.AmbQ . (:[])) $
     filter (not . extendedLambda) $
     universeBi decl) ++
    universeBi decl
    where
    extendedLambda :: A.QName -> Bool
    extendedLambda = (extendedLambdaName `isPrefixOf`) . show . A.nameConcrete . A.qnameName

  -- Bound variables, dotted patterns, record fields, module names,
  -- the "as" and "to" symbols.
  theRest modMap file = mconcat
    [ Fold.foldMap getFieldDecl   $ universeBi decl
    , Fold.foldMap getVarAndField $ universeBi decl
    , Fold.foldMap getLet         $ universeBi decl
    , Fold.foldMap getLam         $ universeBi decl
    , Fold.foldMap getTyped       $ universeBi decl
    , Fold.foldMap getPattern     $ universeBi decl
    , Fold.foldMap getExpr        $ universeBi decl
    , Fold.foldMap getPatSynArgs  $ universeBi decl
    , Fold.foldMap getModuleName  $ universeBi decl
    , Fold.foldMap getModuleInfo  $ universeBi decl
    , Fold.foldMap getNamedArg    $ universeBi decl
    ]
    where
    bound n = nameToFile modMap file [] (A.nameConcrete n)
                         (\isOp -> mempty { aspect = Just $ Name (Just Bound) isOp })
                         (Just $ A.nameBindingSite n)

    patsyn n = nameToFileA modMap file n True $ \isOp ->
                  mempty { aspect = Just $ Name (Just $ Constructor Common.Inductive) isOp }

    macro n = nameToFileA modMap file n True $ \isOp ->
                  mempty { aspect = Just $ Name (Just Macro) isOp }

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
    getVarAndField (A.Var x)            = bound x
    getVarAndField (A.Rec       _ fs)   = mconcat [ field [] x | Left (FieldAssignment x _) <- fs ]
    getVarAndField (A.RecUpdate _ _ fs) = mconcat [ field [] x |      (FieldAssignment x _) <- fs ]
    getVarAndField _                    = mempty

    -- Ulf, 2014-04-09: It would be nicer to have it on Named_ a, but
    -- you can't have polymorphic functions in universeBi.
    getNamedArg :: Common.RString -> File
    getNamedArg x = singleton (rToR $ P.getRange x) mempty{ aspect = Just $ Name (Just Argument) False }

    getLet :: A.LetBinding -> File
    getLet (A.LetBind _ _ x _ _) = bound x
    getLet A.LetPatBind{}        = mempty
    getLet A.LetApply{}          = mempty
    getLet A.LetOpen{}           = mempty

    getLam :: A.LamBinding -> File
    getLam (A.DomainFree _ x) = bound x
    getLam (A.DomainFull {})  = mempty

    getTyped :: A.TypedBinding -> File
    getTyped (A.TBind _ xs _) = mconcat $ map (bound . dget) xs
    getTyped A.TLet{}         = mempty

    getPatSynArgs :: A.Declaration -> File
    getPatSynArgs (A.PatternSynDef _ xs _) = mconcat $ map (bound . Common.unArg) xs
    getPatSynArgs _                        = mempty

    getPattern :: A.Pattern -> File
    getPattern (A.VarP x)    = bound x
    getPattern (A.AsP _ x _) = bound x
    getPattern (A.DotP pi _) =
      singleton (rToR $ P.getRange pi)
                (mempty { otherAspects = [DottedPattern] })
    getPattern (A.PatternSynP _ q _) = patsyn q
    getPattern (A.RecP _ fs) = mconcat [ field [] x | FieldAssignment x _ <- fs ]
    getPattern _             = mempty

    getExpr :: A.Expr -> File
    getExpr (A.PatternSyn q) = patsyn q
    getExpr (A.Macro q)      = macro q
    getExpr _                = mempty

    getFieldDecl :: A.Declaration -> File
    getFieldDecl (A.RecDef _ _ _ _ _ _ _ fs) = Fold.foldMap extractField fs
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
generateTokenInfo file =
  liftIO $ tokenHighlighting <$> Pa.parseFile' Pa.tokensParser file

-- | Same as 'generateTokenInfo' but takes a string instead of a filename.
generateTokenInfoFromString :: P.Range -> String -> TCM CompressedFile
generateTokenInfoFromString r _ | r == P.noRange = return mempty
generateTokenInfoFromString r s = do
  liftIO $ tokenHighlighting <$> Pa.parsePosString Pa.tokensParser p s
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
             -- ^ This should only be @'Full'@ if
             -- type-checking completed successfully (without any
             -- errors).
          -> A.Declaration
          -> TCM NameKinds
nameKinds hlLevel decl = do
  imported <- fix <$> use stImports
  local    <- case hlLevel of
    Full{} -> fix <$> use stSignature
    _      -> return HMap.empty
      -- Traverses the syntax tree and constructs a map from qualified
      -- names to name kinds. TODO: Handle open public.
  let syntax = foldr ($) HMap.empty $ map declToKind $ universeBi decl
  let merged = unions [local, imported, syntax]
  return (\n -> HMap.lookup n merged)
  where
  fix = HMap.map (defnToKind . theDef) . sigDefinitions

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
  defnToKind d@M.Function{} | isProperProjection d = Field
                            | otherwise            = Function
  defnToKind   M.Datatype{}                        = Datatype
  defnToKind   M.Record{}                          = Record
  defnToKind   M.Constructor{ M.conInd = i }       = Constructor i
  defnToKind   M.Primitive{}                       = Primitive

  declToKind :: A.Declaration ->
                HashMap A.QName NameKind -> HashMap A.QName NameKind
  declToKind (A.Axiom _ i _ q _)
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
  declToKind (A.FunDef  _ q _ _)     = insert q Function
  declToKind (A.UnquoteDecl _ _ q _) = insert q Function
  declToKind (A.UnquoteDef _ q _)    = insert q Function
  declToKind (A.DataSig _ q _ _)    = insert q Datatype
  declToKind (A.DataDef _ q _ cs)   = \m ->
                                      insert q Datatype $
                                      foldr (\d -> insert (A.axiomName d)
                                                          (Constructor Common.Inductive))
                                            m cs
  declToKind (A.RecSig _ q _ _)     = insert q Record
  declToKind (A.RecDef _ q _ _ c _ _ _) = insert q Record .
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
  ifNull (P.getRange decl) (return mempty) $ \ (P.Range is) -> do
    let start = fromIntegral $ P.posPos $ P.iStart $ head is
        end   = fromIntegral $ P.posPos $ P.iEnd   $ last is

    -- Get all disambiguated names that fall within the range of decl.
    m0 <- use stDisambiguatedNames
    let (_, m1) = IntMap.split (pred start) m0
        (m2, _) = IntMap.split end m1
        constrs = IntMap.elems m2

    -- Return suitable syntax highlighting information.
    let files = for constrs $ \ q -> generate modMap file kinds $ A.AmbQ [q]
    return $ Fold.fold files

printSyntaxInfo :: P.Range -> TCM ()
printSyntaxInfo r = do
  syntaxInfo <- use stSyntaxInfo
  ifTopLevelAndHighlightingLevelIs NonInteractive $
      printHighlightingInfo (selectC r syntaxInfo)


-- | Prints syntax highlighting info for an error.

printErrorInfo :: TCErr -> TCM ()
printErrorInfo e = printHighlightingInfo . compress =<< errorHighlighting e

-- | Generate highlighting for error.
--   Does something special for termination errors.

errorHighlighting :: TCErr -> TCM File

errorHighlighting (TypeError s cl@(Closure sig env scope (TerminationCheckFailed termErrs))) =
  -- For termination errors, we keep the previous highlighting,
  -- just additionally mark the bad calls.
  return $ terminationErrorHighlighting termErrs

errorHighlighting e = do

  -- Erase previous highlighting.
  let r     = P.getRange e
      erase = singleton (rToR $ P.continuousPerLine r) mempty

  -- Print new highlighting.
  s <- E.prettyError e
  let error = singleton (rToR r)
         $ mempty { otherAspects = [Error]
                  , note         = Just s
                  }
  return $ mconcat [ erase, error ]

-- | Generate syntax highlighting for termination errors.

terminationErrorHighlighting :: [TerminationError] -> File
terminationErrorHighlighting termErrs = functionDefs `mappend` callSites
  where
    m            = mempty { otherAspects = [TerminationProblem] }
    functionDefs = Fold.foldMap (\x -> singleton (rToR $ bindingSite x) m) $
                   concatMap M.termErrFunctions termErrs
    callSites    = Fold.foldMap (\r -> singleton (rToR r) m) $
                   concatMap (map M.callInfoRange . M.termErrCalls) termErrs

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
           -> (Bool -> Aspects)
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
    return (mod, fromIntegral p)

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
             m
             (if include then Just $ bindingSite x else Nothing)

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
  stDisambiguatedNames %= IntMap.insert i q
  where
    start (P.Range [])    = Nothing
    start (P.Range (i:_)) = Just $ fromIntegral $ P.posPos $ P.iStart i
    -- TODO: Move start to Agda.Syntax.Position

------------------------------------------------------------------------
-- All tests

-- | All the properties.

tests :: IO Bool
tests = runTests "Agda.Interaction.Highlighting.Generate" []
