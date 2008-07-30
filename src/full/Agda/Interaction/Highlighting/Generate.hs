{-# LANGUAGE Rank2Types #-}

-- | Generates data used for precise syntax highlighting.

module Agda.Interaction.Highlighting.Generate
  ( TypeCheckingState(..)
  , generateSyntaxInfo
  , generateErrorInfo
  , Agda.Interaction.Highlighting.Generate.tests
  )
  where

import Agda.Interaction.Highlighting.Precise hiding (tests)
import Agda.Interaction.Highlighting.Range   hiding (tests)
import Agda.TypeChecking.Monad
  hiding (MetaInfo, Primitive, Constructor, Record, Function, Datatype)
import qualified Agda.TypeChecking.Monad as M
import qualified Agda.TypeChecking.Reduce as R
import qualified Agda.Syntax.Abstract as A
import qualified Agda.Syntax.Concrete as C
import qualified Agda.Syntax.Internal as I
import qualified Agda.Syntax.Literal as L
import qualified Agda.Syntax.Parser as Pa
import qualified Agda.Syntax.Parser.Tokens as T
import qualified Agda.Syntax.Position as P
import qualified Agda.Syntax.Scope.Base as S
import qualified Agda.Syntax.Translation.ConcreteToAbstract as CA
import Agda.Utils.TestHelpers
import Control.Monad
import Control.Monad.Trans
import Control.Applicative
import Data.Monoid
import Data.Generics
import Data.Function
import Agda.Utils.Generics
import Agda.Utils.FileName
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Sequence (Seq, (><))
import Data.List ((\\))
import qualified Data.Sequence as Seq
import qualified Data.Foldable as Fold (toList, fold, foldMap)
import qualified Data.Traversable as Trav (mapM)

-- | Generates syntax highlighting information for an error,
-- represented as a range and a string.

generateErrorInfo :: P.Range -> String -> File
generateErrorInfo r s =
  several (rToR r) (mempty { otherAspects = [Error], note = Just s })

-- | Has typechecking been done yet?

data TypeCheckingState = TypeCheckingDone | TypeCheckingNotDone
  deriving (Show, Eq)

-- | Generates syntax highlighting information.

generateSyntaxInfo
  :: FilePath               -- ^ The module to highlight.
  -> TypeCheckingState      -- ^ Has it been type checked?
  -> CA.TopLevelInfo        -- ^ The abstract syntax of the module.
  -> [([A.QName], [Range])] -- ^ Functions which failed to termination
                            --   check (grouped if they are mutual),
                            --   along with ranges for problematic
                            --   call sites.
  -> TCM File
generateSyntaxInfo file tcs top termErrs =
  M.withScope_ (CA.insideScope top) $ M.ignoreAbstractMode $ do
    tokens   <- liftIO $ Pa.parseFile' Pa.tokensParser file
    nameInfo <- fmap mconcat $ mapM (generate file tcs) (Fold.toList names)
    -- Constructors are only highlighted after type checking, since they
    -- can be overloaded.
    constructorInfo <- if tcs == TypeCheckingNotDone
                          then return mempty
                          else generateConstructorInfo file decls
    metaInfo <- if tcs == TypeCheckingNotDone
                   then return mempty
                   else computeUnsolvedMetaWarnings
    -- theRest need to be placed before nameInfo here since record field
    -- declarations contain QNames. tokInfo is placed last since token
    -- highlighting is more crude than the others.
    return $ mconcat [ constructorInfo
                     , theRest
                     , nameInfo
                     , metaInfo
                     , termInfo
                     , tokInfo tokens
                     ]
  where
    decls = CA.topLevelDecls top

    tokInfo = Fold.foldMap tokenToFile
      where
      aToF a r = several (rToR r) (mempty { aspect = Just a })

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
                     concatMap fst termErrs
      callSites    = Fold.foldMap (\r -> singleton r m) $
                     concatMap snd termErrs

    -- All names mentioned in the syntax tree (not ambiguous ones, and
    -- not bound variables).
    names = everything' (><) (Seq.empty `mkQ` getName) decls
      where
      getName :: A.QName -> Seq A.QName
      getName n = Seq.singleton n

    -- Bound variables, dotted patterns, record fields and module
    -- names.
    theRest = everything' mappend query decls
      where
      query :: GenericQ File
      query = mempty         `mkQ`
              getFieldDecl   `extQ`
              getVarAndField `extQ`
              getLet         `extQ`
              getLam         `extQ`
              getTyped       `extQ`
              getPattern     `extQ`
              getModuleName

      bound n = nameToFile file []
                           (A.nameConcrete n)
                           (\isOp -> mempty { aspect = Just $ Name (Just Bound) isOp })
                           (Just $ A.nameBindingSite n)
      field m n = nameToFile file m n
                             (\isOp -> mempty { aspect = Just $ Name (Just Field) isOp })
                             Nothing
      mod n = nameToFile file []
                         (A.nameConcrete n)
                         (\isOp -> mempty { aspect = Just $ Name (Just Module) isOp })
                         (Just $ A.nameBindingSite n)

      getVarAndField :: A.Expr -> File
      getVarAndField (A.Var x)    = bound x
      getVarAndField (A.Rec _ fs) = mconcat $ map (field [] . fst) fs
      getVarAndField _            = mempty

      getLet :: A.LetBinding -> File
      getLet (A.LetBind _ x _ _) = bound x
      getLet A.LetApply{}        = mempty

      getLam :: A.LamBinding -> File
      getLam (A.DomainFree _ x) = bound x
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

      getFieldDecl :: A.Definition -> File
      getFieldDecl (A.RecDef _ _ _ _ fs) = Fold.foldMap extractField fs
        where
        extractField (A.ScopedDecl _ ds) = Fold.foldMap extractField ds
        extractField (A.Field _ x _)     = field (concreteQualifier x)
                                                 (concreteBase x)
        extractField _                   = mempty
      getFieldDecl _                   = mempty

      getModuleName :: A.ModuleName -> File
      getModuleName (A.MName { A.mnameToList = xs }) =
        mconcat $ map mod xs

-- | Generates syntax highlighting information for all constructors
-- occurring in patterns and expressions in the given declarations.
--
-- This function should only be called after type checking.
-- Constructors can be overloaded, and the overloading is resolved by
-- the type checker.

generateConstructorInfo :: FilePath -- ^ The module to highlight.
                        -> [A.Declaration]
                        -> TCM File
generateConstructorInfo file decls = do
  -- Extract all defined names from the declaration list.
  let names = Fold.toList $ Fold.foldMap A.allNames decls

  -- Look up the corresponding declarations in the internal syntax.
  defMap <- M.sigDefinitions <$> M.getSignature
  let defs = catMaybes $ map (flip Map.lookup defMap) names

  -- Instantiate meta variables.
  clauses <- mapM R.instantiateFull $ concatMap M.defClauses defs
  types   <- mapM (R.instantiateFull . defType) defs

  -- Find all constructors occurring in type signatures or clauses
  -- within the given declarations.
  let constrs = everything' (><) query (types, clauses)

  -- Return suitable syntax highlighting information.
  Fold.fold <$> Trav.mapM (generate file TypeCheckingDone) constrs
  where
  query :: GenericQ (Seq A.QName)
  query = mempty          `mkQ`
          getConstructor  `extQ`
          getConstructorP

  getConstructor :: I.Term -> Seq A.QName
  getConstructor (I.Con q _) = Seq.singleton q
  getConstructor _           = Seq.empty

  getConstructorP :: I.Pattern -> Seq A.QName
  getConstructorP (I.ConP q _) = Seq.singleton q
  getConstructorP _            = Seq.empty

-- | Generates syntax highlighting information for unsolved meta
-- variables.

computeUnsolvedMetaWarnings :: TCM File
computeUnsolvedMetaWarnings = do
  is <- getInteractionMetas
  ms <- getOpenMetas
  rs <- mapM getMetaRange (ms \\ is)
  return $ several (concatMap rToR rs)
         $ mempty { otherAspects = [UnsolvedMeta] }

-- | Generates a suitable file for a name.

generate :: FilePath
            -- ^ The module to highlight.
         -> TypeCheckingState
            -- ^ Some information can only be generated after type
            -- checking. (This can probably be improved.)
         -> A.QName
         -> TCM File
generate file tcs n = do
  mNameKind <- if tcs == TypeCheckingDone then
                fmap (Just . toAspect . theDef) $ getConstInfo n
               else
                return Nothing
  let m isOp = mempty { aspect = Just $ Name mNameKind isOp }
  return (nameToFileA file n m)
  where
  toAspect :: Defn -> NameKind
  toAspect (M.Axiom {})       = Postulate
  toAspect (M.Function {})    = Function
  toAspect (M.Datatype {})    = Datatype
  toAspect (M.Record {})      = Record
  toAspect (M.Constructor {}) = Constructor
  toAspect (M.Primitive {})   = Primitive

-- | Converts names to suitable 'File's.

nameToFile :: FilePath
              -- ^ The file name of the current module. Used for
              -- consistency checking.
           -> [C.Name]
              -- ^ The name qualifier (may be empty).
              --
              -- This argument is currently ignored.
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
nameToFile file xs x m mR =
  case fmap P.srcFile $ P.rStart $ P.getRange x of
    -- Ignore names whose ranges indicate that they were used in
    -- another file. TODO: This probably indicates an error.
    Just f | not (f =^= file) -> mempty
    _ -> several rs' ((m isOp) { definitionSite = mFilePos =<< mR })
  where
  (=^=)      = (==) `on` last . splitPath
  (rs, isOp) = getRanges x
  rs'        = rs -- ++ concatMap (fst . getRanges) xs
  mFilePos r = fmap extract (P.rStart r)
    where
    extract (P.Pn { P.srcFile = f, P.posPos = p }) = (f, toInteger p)

-- | A variant of 'nameToFile' for qualified abstract names.

nameToFileA :: FilePath
               -- ^ The file name of the current module. Used for
               -- consistency checking.
            -> A.QName
               -- ^ The name.
            -> (Bool -> MetaInfo)
               -- ^ Meta information to be associated with the name.
               -- ^ The argument is 'True' iff the name is an operator.
            -> File
nameToFileA file x m =
  nameToFile file
             (concreteQualifier x)
             (concreteBase x)
             m
             (Just $ bindingSite x)

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
