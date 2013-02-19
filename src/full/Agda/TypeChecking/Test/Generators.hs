{-# LANGUAGE CPP, MultiParamTypeClasses,
             FunctionalDependencies, UndecidableInstances,
             TypeSynonymInstances, FlexibleInstances
  #-}

module Agda.TypeChecking.Test.Generators where

import Control.Applicative
import Control.Monad
import Control.Monad.State
import qualified Data.List as List (sort, nub)
import Agda.Utils.QuickCheck hiding (Args)

import Agda.Syntax.Position
import Agda.Syntax.Common as Common
import Agda.Syntax.Literal
import Agda.Syntax.Fixity
import Agda.Syntax.Internal as I
import qualified Agda.Syntax.Concrete.Name as C
import Agda.TypeChecking.Free
import Agda.TypeChecking.Substitute
import Agda.Utils.TestHelpers
import Agda.Utils.Monad
import Agda.Utils.QuickCheck hiding (Args)
import qualified Agda.Utils.VarSet as Set

#include "../../undefined.h"
import Agda.Utils.Impossible

data TermConfiguration = TermConf
      { tcDefinedNames	   :: [QName]
      , tcConstructorNames :: [QName]
      , tcFreeVariables	   :: [Nat]
      , tcLiterals	   :: UseLiterals
      , tcFrequencies	   :: Frequencies
      , tcFixSize	   :: Maybe Int
	-- ^ Maximum size of the generated element. When @Nothing@ this value
	--   is initialized from the 'Test.QuickCheck.size' parameter.
      , tcIsType	   :: Bool
	-- ^ When this is true no lambdas, literals, or constructors are
	--   generated
      }
  deriving Show

data Frequencies = Freqs
      { hiddenFreqs :: HiddenFreqs
      , nameFreqs   :: NameFreqs
      , sortFreqs   :: SortFreqs
      , termFreqs   :: TermFreqs
      }
  deriving Show

data TermFreqs = TermFreqs
      { nameFreq :: Int
      , litFreq	 :: Int
      , sortFreq :: Int
      , lamFreq	 :: Int
      , piFreq	 :: Int
      , funFreq	 :: Int
      }
  deriving Show

data NameFreqs = NameFreqs
      { varFreq :: Int
      , defFreq :: Int
      , conFreq :: Int
      }
  deriving Show

data HiddenFreqs = HiddenFreqs
      { hiddenFreq    :: Int
      , notHiddenFreq :: Int
      }
  deriving Show

data SortFreqs = SortFreqs
      { setFreqs :: [Int]
      , propFreq :: Int
      }
  deriving Show

defaultFrequencies :: Frequencies
defaultFrequencies = Freqs
      { termFreqs   = TermFreqs	  { nameFreq = 40, litFreq = 1, sortFreq = 2, lamFreq = 10, piFreq = 5, funFreq = 5 }
      , nameFreqs   = NameFreqs	  { varFreq = 3, defFreq = 1, conFreq = 1 }
      , hiddenFreqs = HiddenFreqs { hiddenFreq = 1, notHiddenFreq = 5 }
      , sortFreqs   = SortFreqs	  { setFreqs = [3, 1], propFreq = 1 }
      }

noProp :: TermConfiguration -> TermConfiguration
noProp conf = conf { tcFrequencies = fq { sortFreqs = sfq { propFreq = 0 } } }
  where
    fq	= tcFrequencies conf
    sfq	= sortFreqs fq

data UseLiterals = UseLit
      { useLitInt    :: Bool
      , useLitFloat  :: Bool
      , useLitString :: Bool
      , useLitChar   :: Bool
      }
  deriving Show

noLiterals :: UseLiterals
noLiterals = UseLit False False False False

fixSizeConf :: Int -> TermConfiguration -> TermConfiguration
fixSizeConf n conf = conf { tcFixSize = Just n }

resizeConf :: (Int -> Int) -> TermConfiguration -> TermConfiguration
resizeConf f conf = conf { tcFixSize = fmap f $ tcFixSize conf}

decrConf :: TermConfiguration -> TermConfiguration
decrConf = resizeConf (flip (-) 1)

divConf :: TermConfiguration -> Int -> TermConfiguration
divConf conf k = resizeConf (`div` k) conf

isTypeConf :: TermConfiguration -> TermConfiguration
isTypeConf conf = conf { tcIsType = True }

isntTypeConf :: TermConfiguration -> TermConfiguration
isntTypeConf conf = conf { tcIsType = False }

extendConf :: TermConfiguration -> TermConfiguration
extendConf conf = conf { tcFreeVariables = 0 : map (1+) (tcFreeVariables conf) }

extendWithTelConf :: Telescope -> TermConfiguration -> TermConfiguration
extendWithTelConf tel conf = foldr (const extendConf) conf (telToList tel)

makeConfiguration :: [String] -> [String] -> [Nat] -> TermConfiguration
makeConfiguration ds cs vs = TermConf
  { tcDefinedNames     = defs
  , tcConstructorNames = cons
  , tcFreeVariables    = List.sort $ List.nub vs
  , tcFrequencies      = defaultFrequencies
  , tcLiterals	       = noLiterals
  , tcFixSize	       = Nothing
  , tcIsType	       = False
  }
  where
    (defs, cons) = flip evalState 0 $
		   (,) <$> mapM mkName ds <*> mapM mkName cs

    tick     = do x <- get; put (x + 1); return x
    mkName s = do
      n <- tick
      return $ QName { qnameModule = MName []
		     , qnameName   = Name
			{ nameId	  = NameId n 1
			, nameConcrete	  = C.Name noRange [C.Id s]
			, nameBindingSite = noRange
			, nameFixity	  = defaultFixity'
			}
		      }

class GenC a where
  genC :: TermConfiguration -> Gen a

newtype YesType a   = YesType	{ unYesType :: a     }
newtype NoType  a   = NoType	{ unNoType  :: a     }
newtype VarName	    = VarName	{ unVarName :: Nat   }
newtype DefName	    = DefName	{ unDefName :: QName }
newtype ConName	    = ConName	{ unConName :: QName }
newtype SizedList a = SizedList { unSizedList :: [a] }

fixSize :: TermConfiguration -> Gen a -> Gen a
fixSize conf g = sized $ \n -> resize (maybe n id $ tcFixSize conf) g

instance GenC a => GenC (SizedList a) where
  genC conf = do
    n <- fixSize conf natural
    SizedList <$> vectorOf n (genC $ divConf conf n)

instance GenC a => GenC [a] where
  genC conf = do
    n <- natural
    vectorOf n $ genC $ divConf conf n

instance (GenC a, GenC b) => GenC (a, b) where
  genC conf = (,) <$> genC conf2 <*> genC conf2
    where
      conf2 = divConf conf 2

instance GenC Range where
  genC _ = return noRange

instance GenC Hiding where
  genC conf = frequency [ (hideF, return Hidden), (nohideF, return NotHidden) ]
    where
      HiddenFreqs {hiddenFreq = hideF, notHiddenFreq = nohideF } =
	hiddenFreqs $ tcFrequencies conf

instance (GenC c, GenC a) => GenC (Common.Arg c a) where
  genC conf = (\ (h, a) -> Arg (setArgInfoHiding h defaultArgInfo) a) <$> genC conf

instance (GenC c, GenC a) => GenC (Common.Dom c a) where
  genC conf = (\ (h, a) -> Dom (setArgInfoHiding h defaultArgInfo) a) <$> genC conf

instance GenC a => GenC (Abs a) where
  genC conf = Abs "x" <$> genC (extendConf conf)

genArgs :: TermConfiguration -> Gen Args
genArgs conf = unSizedList <$> genC (isntTypeConf conf)

instance GenC Sort where
  genC conf = frequency $
    (propF, return Prop) :
    zip setFs (map (return . mkType) [0..])
    where
      freq f = f $ tcFrequencies conf
      setFs = freq (setFreqs . sortFreqs)
      propF = freq (propFreq . sortFreqs)

instance GenC Char where
  genC _ = elements [' '..'~'] -- TODO

instance GenC Double where
  genC _ = arbitrary

instance GenC Integer where
  genC _ = arbitrary

instance GenC Literal where
  genC conf = oneof (concat $ zipWith gen useLits
	      [ uncurry LitInt	  <$> genC conf
	      , uncurry LitFloat  <$> genC conf
	      , uncurry LitString <$> genC conf
	      , uncurry LitChar   <$> genC conf
	      ]
	   )
    where
      useLits = map ($ tcLiterals conf) [ useLitInt, useLitFloat, useLitString, useLitChar ]

      gen True  g = [g]
      gen False g = []

instance GenC Telescope where
  genC conf = do
    n <- fixSize conf natural
    let confs = take n $ iterate extendConf (divConf conf n)
    telFromList <$> mapM genC confs

instance GenC Type where
  genC conf = El <$> genC conf <*> genC (isTypeConf conf)

instance GenC Term where
  genC conf = case tcFixSize conf of
      Nothing -> sized $ \n -> genC $ fixSizeConf n conf
      Just n | n <= 0    -> genLeaf
	     | otherwise -> frequency
	[ (nameF, genName $ genArgs conf)
	, (litF,  Lit <$> genC conf)
	, (sortF, Sort <$> genC conf)
	, (lamF,  genLam)
	, (piF,	  genPi)
	]
    where
      defs    = tcDefinedNames conf
      cons    = tcConstructorNames conf
      vars    = tcFreeVariables conf
      freq f  = f $ tcFrequencies conf
      isType  = tcIsType conf
      useLits = map ($ tcLiterals conf) [ useLitInt, useLitFloat, useLitString, useLitChar ]

      varF  | null vars = 0
	    | otherwise = freq (varFreq . nameFreqs)
      defF  | null defs = 0
	    | otherwise = freq (defFreq . nameFreqs)
      conF  | null cons || isType = 0
	    | otherwise	       = freq (conFreq . nameFreqs)
      litF  | or useLits && not isType = freq (litFreq . termFreqs)
	    | otherwise		    = 0
      nameF | 0 == varF + defF + conF = 0
	    | otherwise		    = freq (nameFreq . termFreqs)
      lamF  | isType    = 0
	    | otherwise = freq (lamFreq  . termFreqs)
      sortF = freq (sortFreq . termFreqs)
      piF   = freq (piFreq   . termFreqs)

      genLam :: Gen Term
      genLam = Lam <$> (flip setArgInfoHiding defaultArgInfo <$> genC conf) <*> genC (isntTypeConf $ decrConf conf)

      genPi :: Gen Term
      genPi = uncurry Pi <$> genC conf

      genVar, genDef, genCon :: Gen Args -> Gen Term
      genVar args = Var <$> elements vars <*> args
      genDef args = Def <$> elements defs <*> args
      genCon args = Con <$> elements cons <*> args

      genName :: Gen Args -> Gen Term
      genName args = frequency
	[ (varF, genVar args)
	, (defF, genDef args)
	, (conF, genCon args)
	]

      genLeaf :: Gen Term
      genLeaf = frequency
	[ (nameF, genName $ return [])
	, (litF,  Lit  <$> genC conf)
	, (sortF, Sort <$> genC conf)
	]

-- | Only generates default configurations. Names and free variables varies.
genConf :: Gen TermConfiguration
genConf = do
  ds <- listOf $ elements defs
  cs <- listOf $ elements cons
  vs <- listOf natural
  return $ makeConfiguration ds cs vs
  where
    defs = [ [c] | c <- ['a'..'z'] ]
    cons = [ [c] | c <- ['A'..'Z'] ]

instance Arbitrary TermConfiguration where
  arbitrary   = genConf

-- Shrinking --------------------------------------------------------------

class ShrinkC a b | a -> b where
  shrinkC  :: TermConfiguration -> a -> [b]
  noShrink :: a -> b

instance ShrinkC a b => ShrinkC (YesType a) b where
  shrinkC conf (YesType x) = shrinkC (isTypeConf conf) x
  noShrink (YesType x) = noShrink x

instance ShrinkC a b => ShrinkC (NoType a) b where
  shrinkC conf (NoType x) = shrinkC (isntTypeConf conf) x
  noShrink (NoType x) = noShrink x

instance ShrinkC a b => ShrinkC [a] [b] where
  noShrink	  = map noShrink
  shrinkC conf xs = noShrink (removeChunks xs) ++ shrinkOne xs
   where
    -- Code stolen from Test.QuickCheck.Arbitrary
    removeChunks xs = rem (length xs) xs
     where
      rem 0 _  = []
      rem 1 _  = [[]]
      rem n xs = xs1
               : xs2
               : ( [ xs1' ++ xs2 | xs1' <- rem n1 xs1, not (null xs1') ]
             `ilv` [ xs1 ++ xs2' | xs2' <- rem n2 xs2, not (null xs2') ]
                 )
       where
        n1  = n `div` 2
        xs1 = take n1 xs
        n2  = n - n1
        xs2 = drop n1 xs

        []     `ilv` ys     = ys
        xs     `ilv` []     = xs
        (x:xs) `ilv` (y:ys) = x : y : (xs `ilv` ys)

    shrinkOne []     = []
    shrinkOne (x:xs) = [ x' : noShrink xs | x'  <- shrinkC conf x ]
                    ++ [ noShrink x : xs' | xs' <- shrinkOne xs ]

instance (ShrinkC a a', ShrinkC b b') => ShrinkC (a, b) (a', b') where
  noShrink (x, y) = (noShrink x, noShrink y)
  shrinkC conf (x, y) =
    [ (x', noShrink y) | x' <- shrinkC conf x ] ++
    [ (noShrink x, y') | y' <- shrinkC conf y ]

instance ShrinkC VarName Nat where
  shrinkC conf (VarName x) = [ y | y <- tcFreeVariables conf, y < x ]
  noShrink = unVarName

instance ShrinkC DefName QName where
  shrinkC conf (DefName c) = takeWhile (/= c) $ tcDefinedNames conf
  noShrink = unDefName

instance ShrinkC ConName QName where
  shrinkC conf (ConName c) = takeWhile (/= c) $ tcConstructorNames conf
  noShrink = unConName

instance ShrinkC Literal Literal where
  shrinkC _ (LitInt _ 0) = []
  shrinkC conf l	 = LitInt noRange 0 : case l of
      LitInt    r n -> LitInt    r <$> shrink n
      LitString r s -> LitString r <$> shrinkC conf s
      LitChar   r c -> LitChar   r <$> shrinkC conf c
      LitFloat  r x -> LitFloat  r <$> shrink x
      LitQName  r x -> []
  noShrink = id

instance ShrinkC Char Char where
  shrinkC _ 'a' = []
  shrinkC _ _	= ['a']
  noShrink = id

instance ShrinkC Hiding Hiding where
  shrinkC _ Hidden    = [NotHidden]
  shrinkC _ Instance  = [Instance]
  shrinkC _ NotHidden = []
  noShrink = id

instance ShrinkC a b => ShrinkC (Abs a) (Abs b) where
  shrinkC conf (NoAbs s x) = NoAbs s <$> shrinkC conf x
  shrinkC conf (Abs   s x) = Abs s <$> shrinkC (extendConf conf) x
  noShrink = fmap noShrink

instance ShrinkC a b => ShrinkC (I.Arg a) (I.Arg b) where
  shrinkC conf (Arg info x) = (\ (h,x) -> Arg (setArgInfoHiding h info) x) <$> shrinkC conf (argInfoHiding info, x)
  noShrink = fmap noShrink

instance ShrinkC a b => ShrinkC (I.Dom a) (I.Dom b) where
  shrinkC conf (Dom info x) = (\ (h,x) -> Dom (setArgInfoHiding h info) x) <$> shrinkC conf (argInfoHiding info, x)
  noShrink = fmap noShrink

instance ShrinkC a b => ShrinkC (Blocked a) (Blocked b) where
  shrinkC conf (Blocked m x)  = Blocked m <$> shrinkC conf x
  shrinkC conf (NotBlocked x) = NotBlocked <$> shrinkC conf x
  noShrink = fmap noShrink

-- Andreas 2010-09-21: simplify? since Sort Prop is no longer abused as DontCare
instance ShrinkC Sort Sort where
  shrinkC conf Prop = []
  shrinkC conf s = Prop : case s of
    Type n     -> [] -- No Level instance yet -- Type <$> shrinkC conf n
    Prop       -> __IMPOSSIBLE__
    Inf        -> []
    DLub s1 s2 -> __IMPOSSIBLE__
  noShrink = id

instance ShrinkC Telescope Telescope where
  shrinkC conf EmptyTel		 = []
  shrinkC conf (ExtendTel a tel) =
    killAbs tel : (uncurry ExtendTel <$> shrinkC conf (a, tel))
  noShrink = id

instance ShrinkC Type Type where
  shrinkC conf (El s t) = uncurry El <$> shrinkC conf (s, YesType t)
  noShrink = id

instance ShrinkC Term Term where
  shrinkC conf (DontCare _)  = []
  shrinkC conf (Sort Prop) = []
  shrinkC conf t	   = filter validType $ case ignoreSharing t of
    Var i args   -> map unArg args ++
		    (uncurry Var <$> shrinkC conf (VarName i, NoType args))
    Def d args   -> map unArg args ++
		    (uncurry Def <$> shrinkC conf (DefName d, NoType args))
    Con d args   -> map unArg args ++
		    (uncurry Con <$> shrinkC conf (ConName d, NoType args))
    Lit l	 -> Lit <$> shrinkC conf l
    Level l      -> [] -- TODO
    Lam info b   -> killAbs b : ((\(h,x) -> Lam (setArgInfoHiding h defaultArgInfo) x)
                                 <$> shrinkC conf (argInfoHiding info, b))
    Pi a b       -> unEl (unDom a) : unEl (killAbs b) :
		    (uncurry Pi <$> shrinkC conf (a, b))
    Sort s       -> Sort <$> shrinkC conf s
    MetaV m args -> map unArg args ++ (MetaV m <$> shrinkC conf (NoType args))
    DontCare _   -> []
    Shared{}     -> __IMPOSSIBLE__
    where
      validType t
	| not (tcIsType conf) = True
	| otherwise	    = case t of
	    Con _ _ -> False
	    Lam _ _ -> False
	    Lit _	  -> False
	    _	  -> True
  noShrink = id

killAbs :: KillVar a => Abs a -> a
killAbs (Abs   _ x) = killVar 0 x
killAbs (NoAbs _ x) = x

class KillVar a where
  killVar :: Nat -> a -> a

instance KillVar Term where
  killVar i t = case ignoreSharing t of
    Var j args | j == i	   -> DontCare (Var j [])
	       | j >  i	   -> Var (j - 1) $ killVar i args
	       | otherwise -> Var j	  $ killVar i args
    Def c args		   -> Def c	  $ killVar i args
    Con c args		   -> Con c	  $ killVar i args
    Lit l		   -> Lit l
    Level l                -> Level l -- TODO
    Sort s		   -> Sort s
    Lam h b		   -> Lam h	  $ killVar i b
    Pi a b		   -> uncurry Pi  $ killVar i (a, b)
    MetaV m args	   -> MetaV m	  $ killVar i args
    DontCare mv            -> DontCare    $ killVar i mv
    Shared{}               -> __IMPOSSIBLE__

instance KillVar Type where
  killVar i (El s t) = El s $ killVar i t

instance KillVar Telescope where
  killVar i EmptyTel	      = EmptyTel
  killVar i (ExtendTel a tel) = uncurry ExtendTel $ killVar i (a, tel)

instance KillVar a => KillVar (I.Arg a) where
  killVar i = fmap (killVar i)

instance KillVar a => KillVar (I.Dom a) where
  killVar i = fmap (killVar i)

instance KillVar a => KillVar (Abs a) where
  killVar i = fmap (killVar (i + 1))

instance KillVar a => KillVar [a] where
  killVar i = map (killVar i)

instance KillVar a => KillVar (Maybe a) where
  killVar i = fmap (killVar i)

instance (KillVar a, KillVar b) => KillVar (a, b) where
  killVar i (x, y) = (killVar i x, killVar i y)

-- Tests ------------------------------------------------------------------

isWellScoped :: Free a => TermConfiguration -> a -> Bool
isWellScoped conf t = allVars (freeVars t) `Set.isSubsetOf` Set.fromList (tcFreeVariables conf)

-- | Check that the generated terms don't have any out of scope variables.
prop_wellScopedVars :: TermConfiguration -> Property
prop_wellScopedVars conf =
  forAllShrink (genC conf) (shrinkC conf) $ \t ->
  isWellScoped conf (t :: Term)
