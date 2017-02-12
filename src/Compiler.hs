{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
module Compiler
  ( runReaderEnv
  , translate'
  , translateDef
  , translateDef'
  , Term
  , Binding
  , nameToIdent
  ) where

import           Agda.Syntax.Common (NameId)
import           Agda.Syntax.Literal
import           Agda.Syntax.Position
import           Agda.Syntax.Treeless
import           Control.Monad
import           Control.Monad.Extra
import           Control.Monad.Reader
import           Data.Ix
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Tuple.Extra
import           Malfunction.AST
import           Numeric (showHex)
import           Agda.Syntax.Common (NameId(..))

type MonadTranslate m = (MonadReader Env m)

data Env = Env {
  _mapConToTag :: Map QName Int
  , _level :: Int
  }
  deriving (Show)

runReaderEnv :: [[QName]] -> Reader Env a -> a
runReaderEnv allcons ma
  | any ((>rangeSize tagRange) . length) allcons = error "too many constructors"
  | otherwise = ma `runReader` mkEnv
  where
    tagRange = (0, 199)
    mkEnv = Env {
      _mapConToTag = Map.unions [ Map.fromList (zip cons (range tagRange)) | cons <- allcons ]
      , _level = 0
      }

translateDef :: MonadReader Env m => QName -> TTerm -> m Binding
translateDef qnm t
  | isRecursive = do
      tt <- translate t
      return . Recursive . pure $ (nameToIdent qnm, tt)
  | otherwise = do
      tt <- translate t
      return (Named (nameToIdent qnm) tt)
  where
    -- TODO: I don't believe this is enough, consider the example
    -- where functions are mutually recursive.
    --     a = b
    --     b = a
    isRecursive = Set.member qnm (qnamesInTerm t) -- TODO: is this enough?

qnamesInTerm :: TTerm -> Set QName
qnamesInTerm t = go t mempty
  where
    go:: TTerm -> Set QName -> Set QName
    go t qs = case t of
      TDef q -> Set.insert q qs
      TApp f args -> foldr go qs (f:args)
      TLam b -> go b qs
      TCon q -> Set.insert q qs
      TLet a b -> foldr go qs [a, b]
      TCase _ _ p alts -> foldr qnamesInAlt (go p qs) alts
      _  -> qs
      where
        qnamesInAlt a qs = case a of
          TACon q _ t -> Set.insert q (go t qs)
          TAGuard t b -> foldr go qs [t, b]
          TALit _ b -> go b qs

translateDef' :: [[QName]] -> QName -> TTerm -> Binding
translateDef' qs qn = runReaderEnv qs . translateDef qn

translate' :: [[QName]] -> [TTerm] -> [Term]
translate' qs = runReaderEnv qs . mapM translate

translate :: MonadReader Env m => TTerm -> m Term
translate = translateTerm

translateTerm :: MonadTranslate m => TTerm -> m Term
translateTerm tt = case tt of
  TVar i            -> indexToVarTerm i
  TPrim tp          -> return $ wrapPrimInLambda tp
  TDef name         -> return $ translateName name
  TApp t0 args      -> translateApp t0 args
  TLam{}            -> translateLam tt
  TLit lit          -> return $ translateLit lit
  TCon nm           -> translateCon nm []
  TLet t0 t1        -> do
    t0' <- translateTerm t0
    (var, t1') <- introVar (translateTerm t1)
    return (Mlet [Named var t0'] t1')
  -- @def@ is the default value if all @alt@s fail.
  TCase i _ def alts -> do
    t <- indexToVarTerm i
    alts' <- alternatives t
    return $ Mswitch t alts'
    where
      -- Case expressions may not have an alternative, this is encoded
      -- by @def@ being TError TUnreachable.
      alternatives t = case def of
        TError TUnreachable -> mapM (translateSwitch t) alts
        _ -> do
          d <- translateTerm def
          cs <- mapM (translateSwitch t) alts
          return (cs ++ [(anything, d)])
      anything :: [Case]
      anything = [CaseAnyInt, Deftag]
  TUnit             -> return unitT
  TSort             -> error ("Unimplemented " ++ show tt)
  TErased           -> return (Mint (CInt 0)) -- TODO: so... anything can go here?
  TError TUnreachable -> return unreachableT

-- | `unreachableT` is an expression that can never be executed (in a type-
-- correct term), so in malfunction this can be encoded as anything.
unreachableT :: Term
unreachableT = unitT

indexToVarTerm :: MonadReader Env m => Int -> m Term
indexToVarTerm i = do
  ni <- asks _level
  return (Mvar (ident (ni - i - 1)))


translateSwitch :: MonadTranslate m => Term -> TAlt -> m ([Case], Term)
translateSwitch tcase alt = case alt of
--  TAGuard c t -> liftM2 (,) (pure <$> translateCase c) (translateTerm t)
  TALit pat body -> do
    b <- translateTerm body
    let c = pure $ litToCase pat
    return (c, b)
  TACon con arity t -> do
    tg <- nameToTag con
    usedFields <- snd <$> introVars arity
      (Set.map (\ix -> arity - ix - 1) . Set.filter (<arity) <$> usedVars t)
    (vars, t') <- introVars arity (translateTerm t)
    let bt = bindFields vars usedFields tcase t'
          -- TODO: It is not clear how to deal with bindings in a pattern
    return (pure tg, bt)
  TAGuard{}      -> return ([], Mvar "TAGuard")

bindFields :: [Ident] -> Set Int -> Term -> Term -> Term
bindFields vars used termc body = case map bind varsRev of
  [] -> body
  binds -> Mlet binds body
  where
    varsRev = zip [0..] (reverse vars)
    arity = length vars
    bind (ix, iden)
      -- Set.member ix used = Named iden (Mfield (arity - ix - 1) termc)
      | Set.member ix used = Named iden (Mfield ix termc)
      | otherwise = Named iden (Mint (CInt 0))

litToCase :: Literal -> Case
litToCase l = case l of
  LitNat _ i -> CaseInt . fromInteger $ i
  _          -> error "Unimplemented"

translateBinding :: MonadTranslate m => Maybe Ident -> TTerm -> m Binding
translateBinding var t =
  (case var of
      Nothing -> Unnamed
      Just var -> Named var) <$> translateTerm t

-- The argument is the lambda itself and not its body.
translateLam :: MonadTranslate m => TTerm -> m Term
translateLam lam = do
  (is, t) <- translateLams lam
  return $ Mlambda is t
  where
    translateLams :: MonadTranslate m => TTerm -> m ([Ident], Term)
    translateLams (TLam body) = do
      (thisVar, (xs, t)) <- introVar (translateLams body)
      return (thisVar:xs, t)
    translateLams e = do
      e' <- translateTerm e
      return ([], e')

introVars :: MonadReader Env m => Int -> m a -> m ([Ident], a)
introVars k ma = do
  (names, env') <- nextIdxs k
  r <- local (const env') ma
  return (names, r)
  where
    nextIdxs :: MonadReader Env m => Int -> m ([Ident], Env)
    nextIdxs k = do
      i0 <- asks _level
      e <- ask
      return (map ident $ reverse [i0..i0 + k - 1], e{_level = _level e + k})

introVar :: MonadReader Env m => m a -> m (Ident, a)
introVar ma = first head <$> introVars 1 ma

-- This is really ugly, but I've done this for the reason mentioned
-- in `translatePrim'`. Note that a similiar "optimization" could be
-- done for chained lambda-expressions:
--   TLam (TLam ...)
translateApp :: MonadTranslate m => TTerm -> [TTerm] -> m Term
translateApp ft xst = case ft of
  TPrim p ->
    case eOp of
      (Left op) -> case xst of
        [t0]     -> Mintop1 op tp <$> translateTerm t0
        _        -> error ("Malformed! Unary: " ++ show op)
      (Right op) -> case xst of
        [t0, t1] -> liftM2 (Mintop2 op tp) (translateTerm t0) (translateTerm t1)
        [t0] -> do
          -- TODO: review this
          -- translate (3*) ==> \x -> 3*x
          (var, t0') <- introVar (translateTerm t0)
          return (Mlambda [var] (Mintop2 op tp (Mvar var) t0' ))
        _        -> error ("Malformed! Binary: " ++ show op ++ "\nxst = " ++ show xst)
    where
      (eOp, tp) = primToOpAndType p
  TCon nm -> translateCon nm xst
  _       -> do
    f <- translateTerm ft
    xs <- mapM translateTerm xst
    return $ Mapply f xs

ident :: Int -> Ident
ident i = "v" ++ show i

translateLit :: Literal -> Term
translateLit l = case l of
  LitNat _ x -> Mint (CBigint x)
  LitString _ s -> Mstring s
  LitChar _ c-> Mint . CInt . fromEnum $ c
  _ -> error "unsupported literal type"

primToOpAndType :: TPrim -> (Either UnaryIntOp BinaryIntOp, IntType)
primToOpAndType tp = (op, aType)
  where
    op = case tp of
      PAdd -> Right Add
      PSub -> Right Sub
      PMul -> Right Mul
      PQuot -> wrong
      PRem -> Right Mo
      PGeq -> Right Gt
      PLt -> wrong
      PEqI -> wrong
      PEqF -> wrong
      PEqS -> wrong
      PEqC -> wrong
      PEqQ -> wrong
      PIf -> wrong
      PSeq -> wrong
    aType = TInt
    -- TODO: Stub!
    wrong = Right Xor

-- This function wraps primitives in a lambda.
--
--   TPrim PAdd          (abstract syntax, treeless)
--
-- Translates to this:
--
--   lambda a b (+ a b)  (concrete syntax, malfunction)
wrapPrimInLambda :: TPrim -> Term
wrapPrimInLambda tprim = case op of
  Left  unop -> Mlambda [var0]       $ Mintop1 unop tp (Mvar var0)
  Right biop -> Mlambda [var0, var1] $ Mintop2 biop tp (Mvar var0) (Mvar var1)
  where
    (op, tp) = primToOpAndType tprim
    -- TODO: The variables declared here might shadow existing bindings.
    var0  = "n"
    var1  = "m"

-- FIXME: Please not the multitude of interpreting QName in the following
-- section. This may be a problem.
-- This is due to the fact that QName can refer to constructors and regular
-- bindings, I think we want to handle these two cases separately.

-- Questionable implementation:
nameToTag :: MonadReader Env m => QName -> m Case
nameToTag nm = do
  e <- ask
  ifM (isConstructor nm)
    (Tag <$> constrTag nm)
    (error $ "nameToTag only implemented for constructors, qname=" ++ show nm
     ++ "\nenv:" ++ show e)
    -- (return . Tag . fromEnum . nameId . qnameName $ nm)


isConstructor :: MonadReader Env m => QName -> m Bool
isConstructor nm = (nm`Map.member`) <$> asks _mapConToTag

-- |
-- Set of indices of the variables that are referenced inside the term.
--
-- Example
-- λλ Env{_level = 2} usedVars (λ(λ ((Var 3) (λ (Var 4)))) ) == {1}
usedVars :: MonadReader Env m => TTerm -> m (Set Int)
usedVars term = asks _level >>= go mempty term
   where
     go vars t topnext = goterm vars t
       where
         goterms vars = foldM (\acvars tt -> goterm acvars tt) vars
         goterm vars t = do
           nextix <- asks _level
           case t of
             (TVar v) -> return $ govar vars v nextix
             (TApp t args) -> goterms vars (t:args)
             (TLam t) -> snd <$> introVar (goterm vars t)
             (TLet t1 t2) -> do
               vars1 <- goterm vars t1
               snd <$> introVar (goterm vars1 t2)
             (TCase v _ def alts) -> do
               vars1 <- goterm (govar vars v nextix) def
               foldM (\acvars alt -> goalt acvars alt) vars1 alts
             _ -> return vars
         govar vars v nextix
           | 0 <= v' && v' < topnext = Set.insert v' vars
           | otherwise = vars
           where v' = v + topnext - nextix
         goalt vars alt = case alt of
           TACon _ _ b -> goterm vars b
           TAGuard g b -> goterms vars [g, b]
           TALit{} -> return vars


-- TODO: Translate constructors differently from names.
-- Don't know if we should do the same when translating TDef's, but here we
-- should most likely use malfunction "blocks" to represent constructors
-- in an "untyped but injective way". That is, we only care that each
-- constructor maps to a unique number such that we will be able to
-- distinguish it in malfunction. This also means that we should carry
-- some state around mapping each constructor to it's corresponding
-- "block-representation".
--
-- An example for clarity. Consider type:
--
--   T a b = L a | R b | B a b | E
--
-- We need to encode the constructors in an injective way and we need to
-- encode the arity of the constructors as well.
--
--   translate (L a)   = (block (tag 2) (tag 0) a')
--   translate (R b)   = (block (tag 2) (tag 1) b')
--   translate (B a b) = (block (tag 3) (tag 2) a' b')
--   translate E       = (block (tag 1) (tag 3))
translateCon :: MonadTranslate m => QName -> [TTerm] -> m Term
translateCon nm ts = do
  ts' <- mapM translateTerm ts
  tag <- constrTag nm
  return $ Mblock tag ts'

-- Should return a number that unique for this constructor
-- within the data-type.
constrTag :: MonadReader Env m => QName -> m Int
constrTag ns = (Map.! ns) <$> asks _mapConToTag

-- Unit is treated as a glorified value in Treeless, luckily it's fairly
-- straight-forward to encode using the scheme described in the documentation
-- for `translateCon`.
unitT :: Term
unitT = Mblock 0 []

translateName :: QName -> Term
translateName = Mvar . nameToIdent

-- TODO: Update documentatiom:
-- | Translate a Treeless name to a valid identifier in Malfunction
--
-- Not all names in agda are valid names in Treleess. Valid names in Agda are
-- given by [1]. Valid identifiers in Malfunction is subject to change:
--
-- > "Atoms: sequences of ASCII letters, digits, or symbols (the exact set of
-- > allowed symbols isn't quite nailed down yet)"[2]
--
-- This function translates non-alpha-numerical characters to `{n}` where
-- `n` is the ascii-value of that character.
--
-- [1]: http://wiki.portal.chalmers.se/agda/pmwiki.php?n=ReferenceManual2.Identifiers
-- [2]: https://github.com/stedolan/malfunction/blob/master/docs/spec.md
nameToIdent :: QName -> Ident
nameToIdent = t . nameId . qnameName
  where
    t (NameId a b) = hex a ++ "." ++ hex b
    hex = (`showHex` "") . toInteger
