{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
module Compiler (runReaderEnv, translateDef, Term, Binding) where

import           Agda.Syntax.Common (NameId)
import           Agda.Syntax.Literal
import           Agda.Syntax.Position
import           Agda.Syntax.Treeless
import           Control.Monad
import           Control.Monad.Extra
import           Control.Monad.Reader
import           Control.Monad.State
import           Data.Ix
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe
import           Data.Set (Set)
import qualified Data.Set as Set
import           Malfunction.AST

type MonadTranslate m = (MonadState Int m, MonadReader Env m)

data Env = Env {
  _mapConToTag :: Map QName Int
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
    isRecursive = Set.member qnm (qnamesInTerm t) -- TODO: is this enough? think of shadowing

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

translate :: MonadReader Env m => TTerm -> m Term
translate t = translateTerm t `evalStateT` 0

translateTerm :: MonadTranslate m => TTerm -> m Term
translateTerm tt = case tt of
  TVar i            -> return . identToVarTerm $ i
  TPrim tp          -> return $ wrapPrimInLambda tp
  TDef name         -> return $ translateName name
  TApp t0 args      -> translateApp t0 args
  TLam{}            -> translateLam tt
  TLit lit          -> return $ translateLit lit
  TCon nm           -> translateCon nm []
  TLet t0 t1        -> do
    t0' <- translateTerm t0
    var <- freshIdent
    t1' <- translateTerm t1
    return (Mlet [Named var t0'] t1')
  -- @def@ is the default value if all @alt@s fail.
  TCase i _ def alts -> do
    let t = identToVarTerm i
    alts' <- alternatives
    return $ Mswitch t alts'
    where
      -- Case expressions may not have an alternative, this is encoded
      -- by @def@ being TError TUnreachable.
      alternatives = case def of
        TError TUnreachable -> mapM translateSwitch alts
        _ -> do
          d <- translateTerm def
          cs <- mapM translateSwitch alts
          return (cs ++ [(anything, d)])
      anything :: [Case]
      anything = [CaseAnyInt, Deftag]
  TUnit             -> return unitT
  TSort             -> error "Unimplemented"
  TErased           -> error "Unimplemented"
  TError err        -> error $ "Error: " ++ show err

identToVarTerm :: Int -> Term
identToVarTerm = Mvar . ident

translateSwitch :: MonadTranslate m => TAlt -> m ([Case], Term)
translateSwitch alt = case alt of
--  TAGuard c t -> liftM2 (,) (pure <$> translateCase c) (translateTerm t)
  TALit pat body -> do
    b <- translateTerm body
    let c = pure $ litToCase pat
    return (c, b)
  TACon n _arity t    -> do
    tg <- nameToTag n
    t' <- translateTerm t
          -- TODO: It is not clear how to deal with bindings in a pattern
    return (pure tg, t')
  TAGuard{}      -> return ([], Mvar "TAGuard")

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
  return $ Mlambda (reverse is) t
  where
    translateLams :: MonadTranslate m => TTerm -> m ([Ident], Term)
    translateLams (TLam body) = do
      x       <- freshIdent
      (xs, t) <- translateLams body
      return (x:xs, t)
    translateLams e = do
      e' <- translateTerm e
      return ([], e')

freshIdent :: MonadState Int m => m Ident
freshIdent = do { x <- ident <$> get ; incr ; return x }


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
        _        -> error "Malformed!"
      (Right op) -> case xst of
        [t0, t1] -> liftM2 (Mintop2 op tp) (translateTerm t0) (translateTerm t1)
        _        -> error "Malformed!"
    where
      (eOp, tp) = primToOpAndType p
  TCon nm -> translateCon nm xst
  _       -> do
    i <- get
    f <- translateTerm ft       `evalStateT` i
    xs <- mapM translateTerm xst `evalStateT` i
    return $ Mapply f xs

incr :: MonadState Int m => m ()
incr = modify succ

ident :: Int -> String
ident i = "v" ++ show i

translateLit :: Literal -> Term
translateLit l = case l of
  LitNat _ x -> Mint (CInt (fromInteger x))
  LitString _ s -> Mstring s
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
nameToTag nm =
  ifM (isConstructor nm)
    (Tag <$> constrTag nm)
    (return . Tag . fromEnum . nameId . qnameName $ nm)


isConstructor :: MonadReader Env m => QName -> m Bool
isConstructor nm = (nm`Map.member`) <$> asks _mapConToTag


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

nameToIdent :: QName -> Ident
nameToIdent = show
