-- | Utility functions used in the Happy parser.

module Agda.Syntax.Parser.Helpers where

import Prelude hiding (null)

import Control.Applicative ( (<|>) )
import Control.Monad.State ( modify' )

import Data.Bifunctor (first, second)
import Data.Char
import qualified Data.List as List
import Data.Maybe
import Data.Semigroup ((<>), sconcat)
import Data.Text (Text)
import qualified Data.Text as T

import Agda.Syntax.Position
import Agda.Syntax.Parser.Monad
import Agda.Syntax.Parser.Lexer
import Agda.Syntax.Parser.Tokens
import Agda.Syntax.Concrete as C
import Agda.Syntax.Concrete.Attribute as CA
import Agda.Syntax.Concrete.Pattern
import Agda.Syntax.Common
import Agda.Syntax.Notation
import Agda.Syntax.Literal

import Agda.TypeChecking.Positivity.Occurrence

import Agda.Utils.Either
import Agda.Utils.Functor
import Agda.Utils.Hash
import Agda.Utils.List ( spanJust, chopWhen, initLast )
import Agda.Utils.List1 ( List1, pattern (:|), (<|) )
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Syntax.Common.Pretty hiding ((<>))
import Agda.Utils.Singleton
import qualified Agda.Utils.Maybe.Strict as Strict
import qualified Agda.Utils.List1 as List1
import qualified Agda.Utils.List2 as List2

import Agda.Utils.Impossible

-- | Grab leading OPTIONS pragmas.
takeOptionsPragmas :: [Declaration] -> Module
takeOptionsPragmas = uncurry Mod . spanJust (\ d -> case d of
  Pragma p@OptionsPragma{} -> Just p
  _                        -> Nothing)

-- | Insert a top-level module if there is none.
--   Also fix-up for the case the declarations in the top-level module
--   are not indented (this is allowed as a special case).
figureOutTopLevelModule :: [Declaration] -> [Declaration]
figureOutTopLevelModule ds =
  case spanAllowedBeforeModule ds of
    -- Andreas 2016-02-01, issue #1388.
    -- We need to distinguish two additional cases.

    -- Case 1: Regular file layout: imports followed by one module. Nothing to do.
    (ds0, [ Module{} ]) -> ds

    -- Case 2: The declarations in the module are not indented.
    -- This is allowed for the top level module, and thus rectified here.
    (ds0, Module r erased m tel [] : ds2) ->
      ds0 ++ [Module r erased m tel ds2]

    -- Case 3: There is a module with indented declarations,
    -- followed by non-indented declarations.  This should be a
    -- parse error and be reported later (see @toAbstract TopLevel{}@),
    -- thus, we do not do anything here.
    (ds0, Module r _ m tel ds1 : ds2) -> ds  -- Gives parse error in scope checker.
    -- OLD code causing issue 1388:
    -- (ds0, Module r m tel ds1 : ds2) -> ds0 ++ [Module r m tel $ ds1 ++ ds2]

    -- Case 4: a top-level module declaration is missing.
    -- Andreas, 2017-01-01, issue #2229:
    -- Put everything (except OPTIONS pragmas) into an anonymous module.
    _ -> ds0 ++ [Module r defaultErased (QName $ noName r) [] ds1]
      where
      (ds0, ds1) = (`span` ds) $ \case
        Pragma OptionsPragma{} -> True
        _ -> False
      -- Andreas, 2017-05-17, issue #2574.
      -- Since the module noName will act as jump target, it needs a range.
      -- We use the beginning of the file as beginning of the top level module.
      r = beginningOfFile $ getRange ds1

-- | Create a name from a string. The boolean indicates whether a part
-- of the name can be token 'constructor'.
mkName' :: Bool -> (Interval, String) -> Parser Name
mkName' constructor' (i, s) = do
    let
      xs = C.stringNameParts s

      -- The keyword constructor can appear as the only NamePart in the
      -- last segment of a qualified name --- Foo.constructor refers to
      -- the constructor of the record Foo.
      constructor = case xs of
        _ :| [] -> constructor'
        _       -> False
      --  The constructor' argument to mkName' determines whether this
      --  is the last segment of a QName, the local variable constructor
      --  additionally takes whether it's the only NamePart into
      --  consideration.

    mapM_ (isValidId constructor) xs
    unless (alternating xs) $ parseError $ "a name cannot contain two consecutive underscores"
    return $ Name (getRange i) InScope xs
    where
        isValidId _ Hole   = return ()
        isValidId con (Id y) = do
          let x = rawNameToString y
              err = "in the name " ++ s ++ ", the part " ++ x ++ " is not valid"
          case parse defaultParseFlags [0] (lexer return) x of
            ParseOk _ TokId{}  -> return ()
            ParseFailed{}      -> parseError err
            ParseOk _ TokEOF{} -> parseError err
            ParseOk _ (TokKeyword KwConstructor _) | con -> pure ()
            ParseOk _ t   -> parseError . ((err ++ " because it is ") ++) $ case t of
              TokQId{}      -> __IMPOSSIBLE__ -- "qualified"
              TokKeyword{}  -> "a keyword"
              TokLiteral{}  -> "a literal"
              TokSymbol s _ -> case s of
                SymDot               -> __IMPOSSIBLE__ -- "reserved"
                SymSemi              -> "used to separate declarations"
                SymVirtualSemi       -> __IMPOSSIBLE__
                SymBar               -> "used for with-arguments"
                SymColon             -> "part of declaration syntax"
                SymArrow             -> "the function arrow"
                SymEqual             -> "part of declaration syntax"
                SymLambda            -> "used for lambda-abstraction"
                SymUnderscore        -> "used for anonymous identifiers"
                SymQuestionMark      -> "a meta variable"
                SymAs                -> "used for as-patterns"
                SymOpenParen         -> "used to parenthesize expressions"
                SymCloseParen        -> "used to parenthesize expressions"
                SymOpenIdiomBracket  -> "an idiom bracket"
                SymCloseIdiomBracket -> "an idiom bracket"
                SymEmptyIdiomBracket -> "an empty idiom bracket"
                SymDoubleOpenBrace   -> "used for instance arguments"
                SymDoubleCloseBrace  -> "used for instance arguments"
                SymOpenBrace         -> "used for hidden arguments"
                SymCloseBrace        -> "used for hidden arguments"
                SymOpenVirtualBrace  -> __IMPOSSIBLE__
                SymCloseVirtualBrace -> __IMPOSSIBLE__
                SymOpenPragma        -> __IMPOSSIBLE__ -- "used for pragmas"
                SymClosePragma       -> __IMPOSSIBLE__ -- "used for pragmas"
                SymEllipsis          -> "used for function clauses"
                SymDotDot            -> __IMPOSSIBLE__ -- "a modality"
                SymEndComment        -> "the end-of-comment brace"
              TokString{}   -> __IMPOSSIBLE__
              TokTeX{}      -> __IMPOSSIBLE__  -- used by the LaTeX backend only
              TokMarkup{}   -> __IMPOSSIBLE__  -- ditto
              TokComment{}  -> __IMPOSSIBLE__
              TokDummy{}    -> __IMPOSSIBLE__

        -- we know that there are no two Ids in a row
        alternating (Hole :| Hole : _) = False
        alternating (_    :| x   : xs) = alternating $ x :| xs
        alternating (_    :|       []) = True

-- | Create a name from a string
mkName :: (Interval, String) -> Parser Name
mkName = mkName' False

-- | Create a qualified name from a list of strings
mkQName :: [(Interval, String)] -> Parser QName
mkQName ss | Just (ss0, ss1) <- initLast ss = do
  xs0 <- mapM mkName ss0
  xs1 <- mkName' True ss1
  return $ foldr Qual (QName xs1) xs0
mkQName _ = __IMPOSSIBLE__ -- The lexer never gives us an empty list of parts

mkDomainFree_ :: (NamedArg Binder -> NamedArg Binder) -> Maybe Pattern -> Name -> NamedArg Binder
mkDomainFree_ f p n = f $ defaultNamedArg $ Binder p $ mkBoundName_ n

mkRString :: (Interval, String) -> RString
mkRString (i, s) = Ranged (getRange i) s

mkRText :: (Interval, String) -> Ranged Text
mkRText (i, s) = Ranged (getRange i) $ T.pack s

-- | Create a qualified name from a string (used in pragmas).
--   Range of each name component is range of whole string.
--   TODO: precise ranges!

pragmaQName :: (Interval, String) -> Parser QName
pragmaQName (r, s) = do
  let ss = chopWhen (== '.') s
  mkQName $ map (r,) ss

mkNamedArg :: Maybe QName -> Either QName Range -> Parser (NamedArg BoundName)
mkNamedArg x y = do
  lbl <- case x of
           Nothing        -> return $ Just $ WithOrigin UserWritten $ unranged "_"
           Just (QName x) -> return $ Just $ WithOrigin UserWritten $ Ranged (getRange x) $ prettyShow x
           _              -> parseError "expected unqualified variable name"
  var <- case y of
           Left (QName y) -> return $ mkBoundName y noFixity'
           Right r        -> return $ mkBoundName (noName r) noFixity'
           _              -> parseError "expected unqualified variable name"
  return $ defaultArg $ Named lbl var

-- | Polarity parser.

polarity :: (Interval, String) -> Parser (Range, Occurrence)
polarity (i, s) =
  case s of
    "_"  -> ret Unused
    "++" -> ret StrictPos
    "+"  -> ret JustPos
    "-"  -> ret JustNeg
    "*"  -> ret Mixed
    _    -> parseError $ "Not a valid polarity: " ++ s
  where
  ret x = return (getRange i, x)

recoverLayout :: [(Interval, String)] -> String
recoverLayout [] = ""
recoverLayout xs@((i, _) : _) = go (iStart i) xs
  where
    c0 = posCol (iStart i)

    go cur [] = ""
    go cur ((i, s) : xs) = padding cur (iStart i) ++ s ++ go (iEnd i) xs

    padding Pn{ posLine = l1, posCol = c1 } Pn{ posLine = l2, posCol = c2 }
      | l1 < l2   = List.genericReplicate (l2 - l1) '\n' ++ List.genericReplicate (max 0 (c2 - c0)) ' '
      | l1 == l2  = List.genericReplicate (c2 - c1) ' '
      | otherwise = __IMPOSSIBLE__

ensureUnqual :: QName -> Parser Name
ensureUnqual (QName x) = return x
ensureUnqual q@Qual{}  = parseError' (rStart' $ getRange q) "Qualified name not allowed here"

------------------------------------------------------------------------
-- Lambinds

-- | Result of parsing @LamBinds@.
data LamBinds' a = LamBinds
  { lamBindings   :: a             -- ^ A number of domain-free or typed bindings or record patterns.
  , absurdBinding :: Maybe Hiding  -- ^ Followed by possibly a final absurd pattern.
  } deriving (Functor)

type LamBinds = LamBinds' [LamBinding]

mkAbsurdBinding :: Hiding -> LamBinds
mkAbsurdBinding = LamBinds [] . Just

mkLamBinds :: a -> LamBinds' a
mkLamBinds bs = LamBinds bs Nothing

-- | Build a forall pi (forall x y z -> ...)
forallPi :: List1 LamBinding -> Expr -> Expr
forallPi bs e = Pi (fmap addType bs) e

-- | Converts lambda bindings to typed bindings.
addType :: LamBinding -> TypedBinding
addType (DomainFull b) = b
addType (DomainFree x) = TBind r (singleton x) $ Underscore r Nothing
  where r = getRange x

-- | Returns the value of the first erasure attribute, if any, or else
-- the default value of type 'Erased'.
--
-- Raises warnings for all attributes except for erasure attributes,
-- and for multiple erasure attributes.

onlyErased
  :: [Attr]  -- ^ The attributes, in reverse order.
  -> Parser Erased
onlyErased as = do
  es <- catMaybes <$> mapM onlyErased' (reverse as)
  case es of
    []     -> return defaultErased
    [e]    -> return e
    e : es -> do
      parseWarning $ MultipleAttributes (getRange es) (Just "erasure")
      return e
  where
  onlyErased' a = case theAttr a of
    RelevanceAttribute{} -> unsup "Relevance"
    CohesionAttribute{}  -> unsup "Cohesion"
    LockAttribute{}      -> unsup "Lock"
    CA.TacticAttribute{} -> unsup "Tactic"
    PolarityAttribute{}  -> unsup "Polarity"
    QuantityAttribute q  -> maybe (unsup "Linearity") (return . Just) $ erasedFromQuantity q
    where
    unsup s = do
      parseWarning $ UnsupportedAttribute (attrRange a) (Just s)
      return Nothing

-- | Constructs extended lambdas.

extLam
  :: Range            -- ^ The range of the lambda symbol and @where@ or
                      --   the braces.
  -> [Attr]           -- ^ The attributes in reverse order.
  -> List1 LamClause  -- ^ The clauses in reverse order.
  -> Parser Expr
extLam symbolRange attrs cs = do
  e <- onlyErased attrs
  let cs' = List1.reverse cs
  return $ ExtendedLam (getRange (symbolRange, e, cs')) e cs'

-- | Constructs extended or absurd lambdas.

extOrAbsLam
  :: Range   -- ^ The range of the lambda symbol.
  -> [Attr]  -- ^ The attributes, in reverse order.
  -> Either ([LamBinding], Hiding) (List1 Expr)
  -> Parser Expr
extOrAbsLam lambdaRange attrs cs = case cs of
  Right es -> do
    -- It is of the form @\ { p1 ... () }@.
    e  <- onlyErased attrs
    cl <- mkAbsurdLamClause False es
    return $ ExtendedLam (getRange (lambdaRange, e, es)) e $ singleton cl
  Left (bs, h) -> do
    mapM_ (\a -> parseWarning $
                   UnsupportedAttribute (attrRange a) Nothing)
          (reverse attrs)
    List1.ifNull bs
      {-then-} (return $ AbsurdLam r h)
      {-else-} $ \ bs -> return $ Lam r bs (AbsurdLam r h)
    where
    r = fuseRange lambdaRange bs

-- | Interpret an expression as a list of names and (not parsed yet) as-patterns

exprAsNamesAndPatterns :: Expr -> Maybe (List1 (Name, Maybe Expr))
exprAsNamesAndPatterns = mapM exprAsNameAndPattern . exprAsTele
  where
    exprAsTele :: Expr -> List1 Expr
    exprAsTele (RawApp _ es) = List2.toList1 es
    exprAsTele e             = singleton e

exprAsNameAndPattern :: Expr -> Maybe (Name, Maybe Expr)
exprAsNameAndPattern (Ident (QName x)) = Just (x, Nothing)
exprAsNameAndPattern (Underscore r _)  = Just (setRange r simpleHole, Nothing)
exprAsNameAndPattern (As _ n e)        = Just (n, Just e)
exprAsNameAndPattern (Paren r e)       = Just (setRange r simpleHole, Just e)
exprAsNameAndPattern _                 = Nothing

-- interpret an expression as name or list of hidden / instance names
exprAsNameOrHiddenNames :: Expr -> Maybe (List1 (NamedArg (Name, Maybe Expr)))
exprAsNameOrHiddenNames = \case
  HiddenArg _ (Named Nothing e) ->
    fmap (hide . defaultNamedArg) <$> exprAsNamesAndPatterns e
  InstanceArg _ (Named Nothing e) ->
    fmap (makeInstance . defaultNamedArg) <$> exprAsNamesAndPatterns e
  e ->
    singleton . defaultNamedArg <$> exprAsNameAndPattern e

boundNamesOrAbsurd :: List1 Expr -> Parser (Either (List1 (NamedArg Binder)) (List1 Expr))
boundNamesOrAbsurd es
  | any isAbsurd es = return $ Right es
  | otherwise       =
    case mapM exprAsNameAndPattern es of
        Nothing   -> parseError $ "expected sequence of bound identifiers"
        Just good -> fmap Left $ forM good $ \ (n, me) -> do
                       p <- traverse exprToPattern me
                       return (defaultNamedArg (Binder p (mkBoundName_ n)))

  where

    isAbsurd :: Expr -> Bool
    isAbsurd (Absurd _)                  = True
    isAbsurd (HiddenArg _ (Named _ e))   = isAbsurd e
    isAbsurd (InstanceArg _ (Named _ e)) = isAbsurd e
    isAbsurd (Paren _ e)                 = isAbsurd e
    isAbsurd (As _ _ e)                  = isAbsurd e
    isAbsurd (RawApp _ es)               = any isAbsurd es
    isAbsurd _                           = False

-- | Match a pattern-matching "assignment" statement @p <- e@
exprToAssignment :: Expr -> Parser (Maybe (Pattern, Range, Expr))
exprToAssignment e@(RawApp r es)
  | (es1, arr : es2) <- List2.break isLeftArrow es =
    case filter isLeftArrow es2 of
      arr : _ -> parseError' (rStart' $ getRange arr) $ "Unexpected " ++ prettyShow arr
      [] ->
        -- Andreas, 2021-05-06, issue #5365
        -- Handle pathological cases like @do <-@ and @do x <-@.
        case (es1, es2) of
          (e1:rest1, e2:rest2) -> do
            p <- exprToPattern $ rawApp $ e1 :| rest1
            pure $ Just (p, getRange arr, rawApp (e2 :| rest2))
          _ -> parseError' (rStart' $ getRange e) $ "Incomplete binding " ++ prettyShow e
  where
    isLeftArrow (Ident (QName (Name _ _ (Id arr :| [])))) =
      arr `elem` ["<-", "\x2190"]  -- \leftarrow [issue #5465, unicode might crash happy]
    isLeftArrow _ = False
exprToAssignment _ = pure Nothing

-- | Build a with-block
buildWithBlock ::
  [Either RewriteEqn (List1 (Named Name Expr))] ->
  Parser ([RewriteEqn], [Named Name Expr])
buildWithBlock rees = case groupByEither rees of
  (Left rs : rest) -> (List1.toList rs,) <$> finalWith rest
  rest             -> ([],) <$> finalWith rest

  where

    finalWith :: (HasRange a, HasRange b) =>
                 [Either (List1 a) (List1 (List1 b))] -> Parser [b]
    finalWith []             = pure $ []
    finalWith [Right ees]    = pure $ List1.toList $ sconcat ees
    finalWith (Right{} : tl) = parseError' (rStart' $ getRange tl)
      "Cannot use rewrite / pattern-matching with after a with-abstraction."
    finalWith (Left{} : _)   = __IMPOSSIBLE__

-- | Build a with-statement
buildWithStmt :: List1 (Named Name Expr) ->
                 Parser [Either RewriteEqn (List1 (Named Name Expr))]
buildWithStmt nes = do
  ws <- mapM buildSingleWithStmt (List1.toList nes)
  let rws = groupByEither ws
  pure $ map (first (Invert ())) rws

buildUsingStmt :: List1 Expr -> Parser RewriteEqn
buildUsingStmt es = do
  mpatexprs <- mapM exprToAssignment es
  case mapM (fmap $ \(pat, _, expr) -> (pat, expr)) mpatexprs of
    Nothing -> parseError' (rStart' $ getRange es) "Expected assignments"
    Just assignments -> pure $ LeftLet assignments

buildSingleWithStmt ::
  Named Name Expr ->
  Parser (Either (Named Name (Pattern, Expr)) (Named Name Expr))
buildSingleWithStmt e = do
  mpatexpr <- exprToAssignment (namedThing e)
  pure $ case mpatexpr of
    Just (pat, _, expr) -> Left ((pat, expr) <$ e)
    Nothing             -> Right e

-- | Build a do-statement
defaultBuildDoStmt :: Expr -> [LamClause] -> Parser DoStmt
defaultBuildDoStmt e (_ : _) = parseError' (rStart' $ getRange e) "Only pattern matching do-statements can have where clauses."
defaultBuildDoStmt e []      = pure $ DoThen e

buildDoStmt :: Expr -> [LamClause] -> Parser DoStmt
buildDoStmt (Let r ds Nothing) [] = return $ DoLet r ds
buildDoStmt e@(RawApp r _)    cs = do
  mpatexpr <- exprToAssignment e
  case mpatexpr of
    Just (pat, r, expr) -> pure $ DoBind r pat expr cs
    Nothing -> defaultBuildDoStmt e cs
buildDoStmt e cs = defaultBuildDoStmt e cs


{--------------------------------------------------------------------------
    Patterns
 --------------------------------------------------------------------------}

-- | Turn an expression into a left hand side.
exprToLHS :: Expr -> Parser ([RewriteEqn] -> [WithExpr] -> LHS)
exprToLHS e = LHS <$> exprToPattern e

-- | Turn an expression into a pattern. Fails if the expression is not a
--   valid pattern.
exprToPattern :: Expr -> Parser Pattern
exprToPattern e = case C.isPattern e of
  Nothing -> parseErrorRange e $ "Not a valid pattern: " ++ prettyShow e
  Just p  -> pure p

-- | Turn an expression into a name. Fails if the expression is not a
--   valid identifier.
exprToName :: Expr -> Parser Name
exprToName (Ident (QName x)) = return x
exprToName e = parseErrorRange e $ "Not a valid identifier: " ++ prettyShow e

-- | When given expression is @e1 = e2@, turn it into a named expression.
--   Call this inside an implicit argument @{e}@ or @{{e}}@, where
--   an equality must be a named argument (rather than a cubical partial match).
maybeNamed :: Expr -> Parser (Named_ Expr)
maybeNamed e =
  case e of
    Equal _ e1 e2 -> do
      let succeed x = return $ named (WithOrigin UserWritten $ Ranged (getRange e1) x) e2
      case e1 of
        Ident (QName x) -> succeed $ nameToRawName x
        -- We could have the following, but names of arguments cannot be _.
        -- Underscore{}    -> succeed $ "_"
        _ -> parseErrorRange e $ "Not a valid named argument: " ++ prettyShow e
    _ -> return $ unnamed e

-- Andreas, 2024-02-20, issue #7136:
-- The following function has been rewritten to a defensive pattern matching style
-- to be robust against future parser changes.
patternSynArgs :: [NamedArg Binder] -> Parser [WithHiding Name]
patternSynArgs = mapM \ x -> do
  let
    abort s = parseError $
      "Illegal pattern synonym argument  " ++ prettyShow x ++ "\n" ++
      "(" ++ s ++ ".)"
    noAnn s = s ++ " annotations not allowed in pattern synonym arguments"

  case x of

    -- Invariant: fixity is not used here, and neither finiteness
    Arg ai (Named mn (Binder mp (BName n fix mtac fin)))
      | not $ null fix -> __IMPOSSIBLE__
      | fin            -> __IMPOSSIBLE__

    -- Error cases:
    Arg _ (Named _ (Binder (Just _) _)) ->
      abort "Arguments to pattern synonyms cannot be patterns themselves"
    Arg _ (Named _ (Binder _ (BName _ _ tac _))) | not (null tac) ->
      abort $ noAnn "Tactic"

    -- Benign case:
    Arg ai (Named mn (Binder Nothing (BName n _ _ _)))
      -- allow {n = n} for backwards compat with Agda 2.6
      | maybe True ((C.nameToRawName n ==) . rangedThing . woThing) mn ->
        case ai of

          -- Benign case:
          ArgInfo h (Modality Relevant{} (Quantityω _) Continuous (PolarityModality { modPolarityAnn = MixedPolarity })) UserWritten UnknownFVs (Annotation IsNotLock) ->
            return $ WithHiding h n

          -- Error cases:
          ArgInfo _ _ _ _ (Annotation (IsLock _)) ->
            abort $ noAnn "Lock"

          ArgInfo h (Modality r q c p) _ _ _
            | not (isRelevant r) ->
                abort "Arguments to pattern synonyms must be relevant"
            | not (isQuantityω q) ->
                abort $ noAnn "Quantity"
            | modPolarityAnn p /= MixedPolarity ->
                abort $ noAnn "Polarity"
            | c /= Continuous ->
                abort $ noAnn "Cohesion"

          -- Invariant: origin and fvs not used.
          ArgInfo _ _ _ (KnownFVs _) _ -> __IMPOSSIBLE__
          ArgInfo _ _ o _ _ | o /= UserWritten -> __IMPOSSIBLE__

          ArgInfo _ _ _ _ _ -> __IMPOSSIBLE__

      -- Error case: other named args are unsupported (issue #7136)
      | otherwise ->
          abort "Arguments to pattern synonyms cannot be named"

mkLamClause
  :: Bool   -- ^ Catch-all?
  -> [Expr] -- ^ Possibly empty list of patterns.
  -> RHS
  -> Parser LamClause
mkLamClause catchAll es rhs = mapM exprToPattern es <&> \ ps ->
  LamClause{ lamLHS = ps, lamRHS = rhs, lamCatchAll = catchAll }

mkAbsurdLamClause :: Bool -> List1 Expr -> Parser LamClause
mkAbsurdLamClause catchAll es = mkLamClause catchAll (List1.toList es) AbsurdRHS

{- RHS or type signature -}

data RHSOrTypeSigs
 = JustRHS RHS
 | TypeSigsRHS Expr
 deriving Show

patternToNames :: Pattern -> Parser (List1 (ArgInfo, Name))
patternToNames = \case
    IdentP _ (QName i)           -> return $ singleton (defaultArgInfo, i)
    WildP r                      -> return $ singleton (defaultArgInfo, C.noName r)
    DotP kwr _ (Ident (QName i)) -> return $ singleton (makeIrrelevant kwr defaultArgInfo, i)
    RawAppP _ ps                 -> sconcat . List2.toList1 <$> mapM patternToNames ps
    p -> parseError $
      "Illegal name in type signature: " ++ prettyShow p

funClauseOrTypeSigs :: [Attr] -> ([RewriteEqn] -> [WithExpr] -> LHS)
                    -> [Either RewriteEqn (List1 (Named Name Expr))]
                    -> RHSOrTypeSigs
                    -> WhereClause -> Parser (List1 Declaration)
funClauseOrTypeSigs attrs lhs' with mrhs wh = do
  (rs , es) <- buildWithBlock with
  let lhs = lhs' rs (map (fmap observeModifiers) es)
  -- traceShowM lhs
  case mrhs of
    JustRHS rhs   -> do
      unless (null attrs) $ parseErrorRange attrs $ "A function clause cannot have attributes"
      return $ singleton $ FunClause lhs rhs wh False
    TypeSigsRHS e -> case wh of
      NoWhere -> case lhs of
        LHS p _ _ | hasEllipsis p -> parseError "The ellipsis ... cannot have a type signature"
        LHS _ _ (_:_) -> parseError "Illegal: with in type signature"
        LHS _ (_:_) _ -> parseError "Illegal: rewrite in type signature"
        LHS p _ _ | hasWithPatterns p -> parseError "Illegal: with patterns in type signature"
        LHS p [] [] -> forMM (patternToNames p) $ \ (info, x) -> do
          info <- applyAttrs attrs info
          return $ typeSig info (getTacticAttr attrs) x e
      _ -> parseError "A type signature cannot have a where clause"

typeSig :: ArgInfo -> TacticAttribute -> Name -> Expr -> Declaration
typeSig i tac n e = TypeSig i tac n (Generalized e)

------------------------------------------------------------------------
-- * Relevance

makeIrrelevant :: (HasRange a, LensRelevance b) => a -> b -> b
makeIrrelevant = setRelevance . Irrelevant . OIrrDot . getRange

makeShapeIrrelevant :: (HasRange a, LensRelevance b) => a -> b -> b
makeShapeIrrelevant = setRelevance . ShapeIrrelevant . OShIrrDotDot . getRange

defaultIrrelevantArg :: HasRange a => a -> b -> Arg b
defaultIrrelevantArg a = makeIrrelevant a . defaultArg

defaultShapeIrrelevantArg :: HasRange a => a -> b -> Arg b
defaultShapeIrrelevantArg a = makeShapeIrrelevant a . defaultArg

------------------------------------------------------------------------
-- * Attributes

-- | Parsed attribute.

data Attr = Attr
  { attrRange :: Range       -- ^ Range includes the @.
  , attrName  :: String      -- ^ Concrete, user written attribute for error reporting.
  , theAttr   :: Attribute   -- ^ Parsed attribute.
  }

instance HasRange Attr where
  getRange = attrRange

instance SetRange Attr where
  setRange r (Attr _ x a) = Attr r x a

-- | Parse an attribute.
toAttribute :: Range -> Expr -> Parser Attr
toAttribute r e = do
  attr <- maybe failure (return . Attr r s) $ exprToAttribute e
  modify' (\ st -> st{ parseAttributes = (theAttr attr, r, s) : parseAttributes st })
  return attr
  where
  s = prettyShow e
  failure = parseErrorRange e $ "Unknown attribute: " ++ s

-- | Apply an attribute to thing (usually `Arg`).
--   This will fail if one of the attributes is already set
--   in the thing to something else than the default value.
applyAttr :: (LensAttribute a) => Attr -> a -> Parser a
applyAttr attr@(Attr _ _ a) = maybe failure return . setPristineAttribute a
  where
  failure = errorConflictingAttribute attr

-- | Apply attributes to thing (usually `Arg`).
--   Expects a reversed list of attributes.
--   This will fail if one of the attributes is already set
--   in the thing to something else than the default value.
applyAttrs :: LensAttribute a => [Attr] -> a -> Parser a
applyAttrs rattrs arg = do
  let attrs = reverse rattrs
  checkForUniqueAttribute (isJust . isQuantityAttribute ) attrs
  checkForUniqueAttribute (isJust . isRelevanceAttribute) attrs
  checkForUniqueAttribute (not . null . isTacticAttribute) attrs
  foldM (flip applyAttr) arg attrs

applyAttrs1 :: LensAttribute a => List1 Attr -> a -> Parser a
applyAttrs1 = applyAttrs . List1.toList

-- | Set the tactic attribute of a binder
setTacticAttr :: List1 Attr -> NamedArg Binder -> NamedArg Binder
setTacticAttr as = updateNamedArg $ fmap $ \ b ->
  case getTacticAttr $ List1.toList as of
    t | null t    -> b
      | otherwise -> b { bnameTactic = t }

-- | Get the tactic attribute if present.
getTacticAttr :: [Attr] -> TacticAttribute
getTacticAttr as = C.TacticAttribute $
  case tacticAttributes [ a | Attr _ _ a <- as ] of
    [CA.TacticAttribute e] -> Just e
    [] -> Nothing
    _  -> __IMPOSSIBLE__

-- | Report a parse error if two attributes in the list are of the same kind,
--   thus, present conflicting information.
checkForUniqueAttribute :: (Attribute -> Bool) -> [Attr] -> Parser ()
checkForUniqueAttribute p attrs = do
  let pAttrs = filter (p . theAttr) attrs
  when (length pAttrs >= 2) $
    errorConflictingAttributes pAttrs

-- | Report an attribute as conflicting (e.g., with an already set value).
errorConflictingAttribute :: Attr -> Parser a
errorConflictingAttribute a = parseErrorRange a $ "Conflicting attribute: " ++ attrName a

-- | Report attributes as conflicting (e.g., with each other).
--   Precondition: List not emtpy.
errorConflictingAttributes :: [Attr] -> Parser a
errorConflictingAttributes [a] = errorConflictingAttribute a
errorConflictingAttributes as  = parseErrorRange as $
  "Conflicting attributes: " ++ unwords (map attrName as)
