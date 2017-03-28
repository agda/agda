#!/bin/bash

# this script is ugly and could use a lot of cleanup

# lengths=`seq 250000 750000 30000000`
lengths=`seq 1000000 2500000 50000000`
execs="MAlonzox Malfunction"
order_types="LRandom"

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


        start_spinner "Compiling MAlonzo"
        cpp AgdaListGen.hs -Dtail -Dlen=$len -D$order > tmp.hs
        stack exec runhaskell -- tmp.hs > TheList.agda
        cpp Fold0.agda Fold.agda
        sed '/^#/ d' Fold.agda -i
        stack exec agda2mlf -- -c RedBlack.agda > /dev/null
        cp RedBlack MAlonzox
        stop_spinner $?

        # start_spinner "Compiling MAlonzo Strict"
        # cpp AgdaListGen.hs -Dtail -Dlen=$len -D$order > tmp.hs
        # stack exec runhaskell -- tmp.hs > TheList.agda
        # cpp Fold0.agda -Dstrict Fold.agda
        # sed '/^#/ d' Fold.agda -i
        # stack exec agda2mlf -- -c RedBlack.agda > /dev/null
        # cp RedBlack MAlonzoStrict
        # stop_spinner $?

        # start_spinner "Compiling Mlf Strict"
        # cpp AgdaListGen.hs -Dtail -Dlen=$len -D$order > tmp.hs
        # stack exec runhaskell -- tmp.hs > TheList.agda
        # cpp Fold0.agda -Dtail -Dstrict Fold.agda
        # sed '/^#/ d' Fold.agda -i
        # stack exec agda2mlf -- --mlf RedBlack.agda --compilemlf=MalfunctionStrict -o RedBlack.mlf > /dev/null
        # stop_spinner $?

        start_spinner "Compiling Mlf"
        cpp AgdaListGen.hs -Dtail -Dlen=$len -D$order > tmp.hs
        stack exec runhaskell -- tmp.hs > TheList.agda
        cpp Fold0.agda -Dtail Fold.agda
        sed '/^#/ d' Fold.agda -i
        stack exec agda2mlf -- --mlf RedBlack.agda --compilemlf=Malfunction -o RedBlack.mlf > /dev/null
        stop_spinner $?


        # start_spinner "Compiling Haskell programs"
        # # ghc RedBlack.hs -O2 -prof -fprof-auto -rtsopts -main-is RedBlack -DRbTypedExist -D$order -DLen=$len -o RbTypedExistProf > /dev/null
        # ghc RedBlack.hs -O2 -main-is RedBlack -DRbUntyped    -D$order -DLen=$len -o HaskUntyped > /dev/null
        # ghc RedBlack.hs -O2 -main-is RedBlack -DRbTyped      -D$order -DLen=$len -o HaskTyped > /dev/null
        # ghc RedBlack.hs -O2 -main-is RedBlack -DRbTypedExist -D$order -DLen=$len -o HaskExistType > /dev/null
        # stop_spinner $?

        # start_spinner "Compiling Strict Haskell programs"
        # ghc RedBlack.hs -O2 -main-is RedBlack -DRbUntyped    -Dstrict -D$order -DLen=$len -o HaskUntypedStrict > /dev/null
        # ghc RedBlack.hs -O2 -main-is RedBlack -DRbTyped      -Dstrict -D$order -DLen=$len -o HaskTypedStrict > /dev/null
        # ghc RedBlack.hs -O2 -main-is RedBlack -DRbTypedExist -Dstrict -D$order -DLen=$len -o HaskExistTypeStrict > /dev/null
        # stop_spinner $?

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
    cp plot.plt $outdir
    (cd $outdir && gnuplot plot.plt)
    echo ""
done
