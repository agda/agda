{-| 

  Call matrices, more or less as defined in
    "A Predicative Analysis of Structural Recursion" by
    Andreas Abel and Thorsten Altenkirch.

-}

module Termination.CallMatrix where

import Prelude hiding ((+), (*), Ord)
import Termination.TestHelpers
import Test.QuickCheck
import Termination.Matrix

------------------------------------------------------------------------
-- Structural orderings

-- Called R in the paper referred to above.

data Ord
  = Lt | Le | Unknown
  deriving (Eq,Show)

instance Arbitrary Ord where
  arbitrary = elements [Lt, Le, Unknown]

  coarbitrary Lt      = variant 0
  coarbitrary Le      = variant 1
  coarbitrary Unknown = variant 2

(+) :: Ord -> Ord -> Ord
Lt      + _  = Lt
Le      + Lt = Lt
Le      + _  = Le
Unknown + o  = o

(*) :: Ord -> Ord -> Ord
Lt      * Unknown = Unknown
Lt      * _       = Lt
Le      * o       = o
Unknown * _       = Unknown

-- (Ord, +, *) forms a semiring.

prop_Ord_semiring = semiring (+) (*) Unknown Le

------------------------------------------------------------------------
-- Call matrices

type CallMatrix = Matrix Ord

{-

compCallMatrix :: CallMatrix -> CallMatrix -> CallMatrix
compCallMatrix cm1 cm2 =
     let m = if isEmptyMatrix cm1 || isEmptyMatrix cm2 
                then matrix (0,0) []
                else multMatrix multTermOrder addTermOrder cm1 cm2
     in m --trace ("mult\n"++(printMatrix cm1)++"\n" ++(printMatrix cm2) ++"\n"++(printMatrix m) ++"\n" ) m




terminates :: [CallMatrix] -> Bool
-- Ändra till en annan terminerings ordning
terminates ms = or [allLt ds i | i <- range (bounds (head  ds))] --trace ("terminates "++show ms) $ 
        where ds :: [Array Int TermOrder] 
              ds  = map diagonal ms
              allLt :: [Array Int TermOrder] -> Int -> Bool
              allLt ds i = all (isLt i) ds --(trace ("terminates2 "++show ds) ds)
              isLt :: Int -> (Array Int TermOrder)  -> Bool
              isLt i a 
                | i `elem` (range (bounds a)) = a!i == Lt
                | otherwise = False



type Call = (UId,UId,CallMatrix)


printCall :: Call -> String
printCall (f,g,m) = "("++ppReadable f++","++ppReadable g++")\n"++ printMatrix m ++ "\n"

compCalls :: [Call] -> [Call] -> [Call]
-- Kolla algoritmen
compCalls [] cs2 = []
compCalls (c:cs1) cs2 = let cs3 = compCall c cs2
                            cs4 = compCalls cs1 cs2
                        in cs3 ++ cs4
    where compCall c [] = []
          compCall c@(f,g,cm) (c2@(f',g',cm'):cs) =
            
              let cs' = compCall c cs
              in if f == g' 
                    then let c' = (f',g,compCallMatrix cm cm')
                         in c':cs'
                    else cs'
                            {-if f' == g
                               then let c2 = (g',f,compCallMatrix cm' cm)
                                    in c':c2:cs'
                               else c':cs'
                          else 
                   
else if f' == g 
                            then let c' = (g',f,compCallMatrix cm' cm)
                                 in c':cs
                            else cs' -}

complete :: [Call] -> [Call]
complete e = complete' e e
   where complete' e0 en = 
              let en' = compCalls en e0
                  en2 = union en en' --(trace ("new "++concatMap printCall en' ++"\n")  en')
              in if en2 == en
                 then en2 --trace ("done "++concatMap printCall en2 ++"\n") en2
                 else complete' e0 en2 --trace ("complete "++concatMap printCall en2++"\n") $ complete' e0 en2 
             


funBehavior :: [Call] -> [(UId,[CallMatrix])]
funBehavior cs = funBehavior'  cs'
          where cs':: [Call]
                cs' = filter sameFun (complete cs)
                funBehavior' :: [Call] -> [(UId,[CallMatrix])]
                funBehavior' [] = []
                funBehavior' ((f,_,m):cs) = let cs2 = funBehavior' cs
                                            in insertFunBehavior f m cs2
                insertFunBehavior f m [] = [(f,[m])]
                insertFunBehavior f m ((g,ms):is) 
                   | f == g = (f,m:ms):is
                   | otherwise = ((g,ms):insertFunBehavior f m is)
                sameFun :: Call -> Bool
                sameFun (f,g,_) = f == g
-}

------------------------------------------------------------------------
-- All tests

tests = do
  quickCheck prop_Ord_semiring
