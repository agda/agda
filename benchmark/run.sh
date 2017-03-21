#!/bin/bash

lengths=`seq 500000 500000 4000000`
# lengths=`seq 50000000 50000000`
execs="RedBlack RedBlackStrict RedBlackMlf RedBlackMlfStrict RbUntyped RbTyped RbTypedExist"

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
order_types="LRandom"
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
        # Generates the definition of the list in agda
        cpp AgdaListGen.hs -Dlen=$len -D$order > tmp.hs
        stack exec runhaskell -- tmp.hs > TheList.agda

        start_spinner "Compiling Agda Strict"
        cpp Fold0.agda -Dstrict Fold.agda
        sed '/^#/ d' Fold.agda -i
        stack exec agda2mlf -- -c RedBlack.agda > /dev/null
        cp RedBlack RedBlackStrict
        stop_spinner $?

        start_spinner "Compiling Mlf Strict"
        stack exec agda2mlf -- --mlf RedBlack.agda --compilemlf=RedBlackMlfStrict -o RedBlack.mlf > /dev/null
        stop_spinner $?


        start_spinner "Compiling Agda"
        cpp Fold0.agda Fold.agda
        sed '/^#/ d' Fold.agda -i
        stack exec agda2mlf -- -c RedBlack.agda > /dev/null
        stop_spinner $?

        start_spinner "Compiling Mlf"
        stack exec agda2mlf -- --mlf RedBlack.agda --compilemlf=RedBlackMlf -o RedBlack.mlf > /dev/null
        stop_spinner $?


        start_spinner "Compiling haskell programs"
        # ghc RedBlack.hs -O2 -prof -fprof-auto -rtsopts -main-is RedBlack -DRbUntyped    -D$order -DLen=$len -o RbUntypedProf > /dev/null
        # ghc RedBlack.hs -O2 -prof -fprof-auto -rtsopts -main-is RedBlack -DRbTyped      -D$order -DLen=$len -o RbTypedProf > /dev/null
        # ghc RedBlack.hs -O2 -prof -fprof-auto -rtsopts -main-is RedBlack -DRbTypedExist -D$order -DLen=$len -o RbTypedExistProf > /dev/null
        ghc RedBlack.hs -O2 -main-is RedBlack -DRbUntyped    -D$order -DLen=$len -o RbUntyped > /dev/null
        ghc RedBlack.hs -O2 -main-is RedBlack -DRbTyped      -D$order -DLen=$len -o RbTyped > /dev/null
        ghc RedBlack.hs -O2 -main-is RedBlack -DRbTypedExist -D$order -DLen=$len -o RbTypedExist > /dev/null
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
    cp plot1.plt $outdir/plot.plt
    (cd $outdir && gnuplot plot.plt)
    echo ""
done
rm $tablefile
