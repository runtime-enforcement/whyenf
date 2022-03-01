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
    OUT=$(../explanator2.native -O ${MEASURE} -mode all -fmla ${PREFIX}.mdl -log ${PREFIX}.log -out_mode debug -check 2>&1 | grep "Checker output: false\|exception")
    if [[ "${OUT}" == *"false"* ]]
    then echo " !! CHECK FAILED !!"
    fi
    if [[ "${OUT}" == *"exception"* ]]
    then echo " !! EXCEPTION RAISED !!"
    fi
}

verb () {
    ./gen_fmla ${PREFIX} ${SIZE} 10 0 1 ${SEED} 16
    ./gen_log ${PREFIX} 100 ${ER} 4 ${SEED} 16
    OUT=$(../explanator2.native -O ${MEASURE} -mode all -fmla ${PREFIX}.mdl -log ${PREFIX}.log -out_mode debug -check 2>&1 | grep "Checker output: false\|exception")
    echo -n "${PREFIX} ... "
    if [[ "${OUT}" == "" ]]
    then echo "OK"
    fi
    if [[ "${OUT}" == *"false"* ]]
    then echo " !! CHECK FAILED !!"
    fi
    if [[ "${OUT}" == *"exception"* ]]
    then echo " !! EXCEPTION RAISED !!"
    fi
}

if [[ "${MODE}" == "simp" ]]
then simp
fi
if [[ "${MODE}" == "verb" ]]
then time verb
fi
