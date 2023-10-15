#!/bin/bash

# ./test_seed.sh verified 10 1 1 4 144

# Input parameters:
SIZE=$2
SCALE=$3
ER=$4
DELTA=$5
SEED=$6

# Flags:
CHECK_FLAG=$1

# Variables:
PREFIX="TMP_${SIZE}_${SCALE}_${ER}_${DELTA}_${SEED}"
OUT=""

usage () {
    printf "usage: test_seed.sh [verified or unverified] [size] [scale] [er] [delta] [seed]\n"
    exit 1
}

verb () {

    ./tmp/gen_fmla ${PREFIX} ${SIZE} 10 0 ${SCALE} ${SEED} 16

    ./tmp/gen_log ${PREFIX} 100 ${ER} ${DELTA} ${SEED} 16
    mv ${PREFIX}.* tmp/

    if [[ "${CHECK_FLAG}" = "verified" ]]
    then
        OUT=$(../bin/whymon.exe -mode verified -sig sig/ap.sig -formula tmp/${PREFIX}.mfotl -log tmp/${PREFIX}.mlog 2>&1)
    else
        if [[ "${CHECK_FLAG}" = "unverified" ]]
        then
            OUT=$(../bin/whymon.exe -mode unverified -sig sig/ap.sig -formula tmp/${PREFIX}.mfotl -log tmp/${PREFIX}.mlog 2>&1)
        else
            usage
        fi
    fi
    OUT_GREP=$(grep "Checker output: false\|exception" <<< "${OUT}")
    N_VERDICTS_WHYMON=$(grep -c "Explanation" <<< "${OUT}")
    N_VERDICTS_VERIMON=$(../../monpoly/monpoly -sig sig/ap.sig -formula tmp/${PREFIX}.mfotl -log tmp/${PREFIX}.log -verified \
                                               -nonewlastts -verbose 2>&1 | grep -c "false\|true")

    printf "${PREFIX} ... "
    if [[ "${OUT_GREP}" == "" ]]
    then printf "OK\n"
    fi
    if [[ "${OUT_GREP}" == *"false"* ]]
    then
        printf " !! CHECK FAILED !!"
    fi
    if [[ "${OUT_GREP}" == *"exception"* ]]
    then
        printf " !! EXCEPTION RAISED !!"
    fi
    if [[ "${N_VERDICTS_WHYMON}" != "${N_VERDICTS_VERIMON}" ]]
    then
        printf "${PREFIX} ... "
        printf " !! N_VERDICTS_WHYMON = ${N_VERDICTS_WHYMON};"
        printf " N_VERDICTS_VERIMON = ${N_VERDICTS_VERIMON} !!\n"
    fi
    printf "\n"
}

if [ "$#" -eq 6 ]
then
    time verb
else
    usage
fi
