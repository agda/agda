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

lengths=`seq 250000 250000 2000000`
execs="RedBlack RedBlackMlf RbUntyped RbTyped"

date=`date`
datedash=${date// /-}
runsdir="runs"
outdir="$runsdir/$datedash"
mkdir -p $outdir
echo $outdir
lengths_file=$outdir/lengths.txt
for len in $lengths
do
    echo $len >> $lengths_file
done

# order_types="LRandom LSorted LRSorted"
order_types="LRSorted LSorted"
time_cmd='/usr/bin/time --format "%e %M"'

# $1 is the name of the executable
# $2 is the order of the list
getOutFile () {
    echo "$outdir/$1-$2.bench"
}

# $1 is the name of the executable
# $2 is the order of the list
bench () {
    outfile=$(getOutFile $1 $2)
    eval "$time_cmd ./$1 > /dev/null 2>> $outfile"
}

source ./spinner.sh
for order in $order_types
do
    echo "--------------------"
    echo "order = $order"
    for len in $lengths
    do
        echo "length = $len"
        # Generates the agda hardcoded list
        cpp AgdaListGen.hs -Dlen=$len -D$order > tmp.hs
        stack exec runhaskell -- tmp.hs > TheList.agda

        start_spinner "Compiling Agda"
        stack exec agda2mlf -- -c RedBlack.agda > /dev/null
        stop_spinner $?

        start_spinner "Compiling Mlf"
        stack exec agda2mlf -- --mlf RedBlack.agda --compilemlf=RedBlackMlf -o RedBlack.mlf > /dev/null
        stop_spinner $?

        start_spinner "Compiling haskell programs"
        ghc RedBlack.hs -O2 -main-is RedBlack -DRbUntyped    -Dlen=$len -o RbUntyped > /dev/null
        ghc RedBlack.hs -O2 -main-is RedBlack -DRbTyped      -Dlen=$len -o RbTyped > /dev/null
        # ghc RedBlack.hs -O2 -main-is RedBlack -DRbTypedExist -Dlen=$len -o RbTypedExist > /dev/null
        stop_spinner $?

        for exec in $execs
        do
            start_spinner "Running $exec, length = $len, order = $order"
            bench $exec $order
            stop_spinner $?
        done
    done
done

headfile=$outdir/head.txt
printf "lengths" > $headfile
for exec in $execs
do
    for meas in time memory
    do
        printf " $exec-$meas" >> $headfile
    done
done
printf "\n" >> $headfile
tablefile=$outdir/table.tmp
for order in $order_types
do
    cat $lengths_file > $tablefile
    for exec in $execs
    do
        file=$(getOutFile $exec $order)
        paste -d " " $tablefile $file > tmp
        mv tmp $tablefile
    done
    allfile=$outdir/$order.data
    cp $headfile $allfile
    cat $tablefile >> $allfile
    printf "\nBenchmark for $order\n"
    cat $allfile
    echo ""
done
rm $tablefile
