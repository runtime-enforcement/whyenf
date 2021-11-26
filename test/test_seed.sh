#!/bin/bash

# ./test_seed 10 2 size 0
# parallel ./test_seed.sh 10 2 size ::: {0..100}

SIZE=$1
ER=$2
MEASURE=$3
MODE=$4
SEED=$5
PREFIX="TMP_${SIZE}_${ER}_${SEED}"

simp () {
    ./gen_fmla ${PREFIX} ${SIZE} 10 0 1 ${SEED} 16
    ./gen_log ${PREFIX} 100 ${ER} 4 ${SEED} 16
    OUT=$(../explanator2.native -O ${MEASURE} -mode all -test -fmla ${PREFIX}.mdl -log ${PREFIX}.log 2>1 | grep "Checker output")
    if [[ "${OUT}" != "" ]]
    then echo "${PREFIX} ... !! FAILED !!"
    fi
}

verb () {
    ./gen_fmla ${PREFIX} ${SIZE} 10 0 1 ${SEED} 16
    ./gen_log ${PREFIX} 100 ${ER} 4 ${SEED} 16
    OUT=$(../explanator2.native -O ${MEASURE} -mode all -test -fmla ${PREFIX}.mdl -log ${PREFIX}.log 2>1 | grep "Checker output")
    echo -n "${PREFIX} ... "
    if [[ "${OUT}" == "" ]]
    then echo "OK"
    fi
    if [[ "${OUT}" != "" ]]
    then echo " !! FAILED !!"
    fi
}

if [[ "${MODE}" == "simp" ]]
then simp
fi
if [[ "${MODE}" == "verb" ]]
then time verb
fi
