#!/bin/sh


# Build sbc-check
if [ ! -f ./sbc-check ]; then
    echo "Build sbc-check"
    cc -O2 -std=c99 -o sbc-check sbc-check.c
fi



run_verification()
{

    name=$1         # formula family name
    id=$2           # id of the instance (e.g. a number)
    cnfgenopt=$3    # parameters for formula gen
    proofgenopt=$4  # parameters for proof gen

    cnfgen $cnfgenopt > $name$id.cnf
    python3 proofgen_$name.py $proofgenopt > $name$id.sbc
    echo "c --------- sbc-check ----------" > $name$id.log
    ./sbc-check $name$id.cnf  $name$id.sbc >> $name$id.log
    echo "c --------- dpr-trim  ----------" >> $name$id.log
    dpr-trim $name$id.cnf $name$id.sbc -f | tr -d '\015' >> $name$id.log

}


# Matching  on bipartite
N=10
run_verification bipmatch $N "php --functional --onto $((N+1)) $N" "$N"

# Matching on grid
N=11
run_verification grid $N "matching grid $N $N" "$N"

# Matching on mutilated chessboard
N=12
run_verification mchess $N "mchess $N $N" "$N"

# Relativized pigeonhole principle
N=4
run_verification rphp $N "rphp $((N+1)) $((N+2)) $N" "$((N+1)) $((N+2)) $N"
