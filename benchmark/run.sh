#!/bin/bash

# limit="120s"
# solverid="0"  # 0=picosat, 1=lingeling
# inst_dir="../instances/"
# tmp_file="out.tmp"

# rm -f $tmp_file
# instances=$(find $inst_dir -name *1.in)
# a=1
# total=$(echo "$instances" | wc -l)
# for f in $instances
# do
#     base=$(basename $f .in)
#     outfile="$inst_dir$base.SAT.out"
#     # drawfile="$inst_dir$base.charmap"
#     timeout $limit $main $inst_dir$f $outfile $solverid >> $tmp_file
#     stop_spinner $?
#     (( a+=1 ))
# done
# solved=$(grep -o Optimal $tmp_file | wc -l)
# echo "number of solved instances within the time limit:"
# echo "$solved out of $total"

lengths="200000 400000 600000 800000 1000000"
# order_types="LRandom LSorted LRSorted"
order_types="LRSorted LSorted"
time_cmd='/usr/bin/time --format "%e %M"'
date=`date`
datedash=${date// /-}
runsdir="runs"
outdir="$runsdir/$datedash"
echo $outdir
# $1 is the name of the executable
# $2 is the order of the list
bench () {
    eval "$time_cmd ./$1 > /dev/null 2>> out-$2.bench"
}

mkdir -p $outdir
source ./spinner.sh
for order in $order_types
do
    echo "order = $order"
    printf "" > out-$order.bench # empty file
    for len in $lengths
    do
        echo "length = $len"
        # Generates the agda hardcoded list
        cpp AgdaListGen.hs -Dlen=$len -D$order > tmp.hs
        stack exec runhaskell -- tmp.hs > TheList.agda

        start_spinner "Compiling Agda"
        # stack exec agda2mlf -- -c RedBlack.agda > /dev/null
        stop_spinner $?

        start_spinner "Compiling Mlf"
        # stack exec agda2mlf -- --mlf RedBlack.agda --compilemlf=RedBlackMlf -o RedBlack.mlf > /dev/null
        stop_spinner $?

        start_spinner "Compiling haskell programs"
        # ghc RedBlack.hs -O2 -main-is RedBlack -DRbUntyped    -Dlen=$len -o RbUntyped > /dev/null
        ghc RedBlack.hs -O2 -main-is RedBlack -DRbTyped      -Dlen=$len -o RbTyped > /dev/null
        # ghc RedBlack.hs -O2 -main-is RedBlack -DRbTypedExist -Dlen=$len -o RbTypedExist > /dev/null
        stop_spinner $?

        start_spinner "Running Agda with MAlonzo backend, length=$len, order=$order"
        # $time_cmd ./RedBlack     > /dev/null
        bench RedBlack $order
        stop_spinner $?

        start_spinner "Running Agda with Ocaml backend, length=$len, order=$order"
        # $time_cmd ./RedBlackMlf  > /dev/null
        bench RedBlackMlf $order
        stop_spinner $?

        start_spinner "Running Haskell Untyped, length=$len, order=$order"
        bench RbUntyped $order
        stop_spinner $?

        start_spinner "Running Haskell Typed, length=$len, order=$order"
        bench RbTyped $order
        stop_spinner $?

        # start_spinner "Running Haskell TypedExist, length=$len, order=$order"
        # bench RbTypedExist $order
        # stop_spinner $?

    done
    cp out-* $outdir
done
