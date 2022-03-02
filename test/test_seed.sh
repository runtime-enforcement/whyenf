#!/bin/bash

# ./test_seed verb 10 1 1 4 size 144
# parallel ./test_seed verb 10 1 1 4 size ::: {0..100}

# Input parameters:
MODE=$1
SIZE=$2
SCALE=$3
ER=$4
DELTA=$5
MEASURE=$6
SEED=$7
PREFIX="TMP_${SIZE}_${SCALE}_${ER}_${DELTA}_${MEASURE}_${SEED}"

simp () {
    ./gen_fmla ${PREFIX} ${SIZE} 10 0 ${SCALE} ${SEED} 16
    ./gen_log ${PREFIX} 100 ${ER} ${DELTA} ${SEED} 16
    OUT=$(../explanator2.native -O ${MEASURE} -mode all -fmla ${PREFIX}.mdl -log ${PREFIX}.log -out_mode debug -check 2>&1 | grep "Checker output: false\|exception")
    if [[ "${OUT}" == *"false"* ]]
    then
        printf "${PREFIX} ... "
        printf " !! CHECK FAILED !!\n"
    fi
    if [[ "${OUT}" == *"exception"* ]]
    then
        printf "${PREFIX} ... "
        printf " !! EXCEPTION RAISED !!\n"
    fi
}

verb () {
    ./gen_fmla ${PREFIX} ${SIZE} 10 0 ${SCALE} ${SEED} 16
    ./gen_log ${PREFIX} 100 ${ER} ${DELTA} ${SEED} 16
    OUT=$(../explanator2.native -O ${MEASURE} -mode all -fmla ${PREFIX}.mdl -log ${PREFIX}.log -out_mode debug -check 2>&1 | grep "Checker output: false\|exception")
    printf "${PREFIX} ... "
    if [[ "${OUT}" == "" ]]
    then printf "OK\n"
    fi
    if [[ "${OUT}" == *"false"* ]]
    then printf " !! CHECK FAILED !!\n"
    fi
    if [[ "${OUT}" == *"exception"* ]]
    then printf " !! EXCEPTION RAISED !!\n"
    fi
}

if [[ "${MODE}" == "simp" ]]
then simp
fi
if [[ "${MODE}" == "verb" ]]
then time verb
fi
