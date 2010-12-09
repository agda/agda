include "Prelude.e"

%inline primNatPlus(x : Int, y : Int) = x+y 
%inline primZero() = 0
%inline primSucc(n : Int) = n+1

%inline primPred(n : Int) = n-1