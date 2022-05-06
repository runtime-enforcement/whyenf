#!/bin/bash

# ./test_seed.sh no-check verb 10 1 1 4 size 144

# Input parameters:
MODE=$2
SIZE=$3
SCALE=$4
ER=$5
DELTA=$6
MEASURE=$7
SEED=$8

# Flags:
CHECK_FLAG=$1

# Variables:
PREFIX="TMP_${SIZE}_${SCALE}_${ER}_${DELTA}_${MEASURE}_${SEED}"
OUT=""

usage () {
    printf "usage: test_seed.sh [check or no-check] [mode] [size] [scale] [er] [delta] [measure] [seed]\n"
    exit 1
}

simp () {
    ./tmp/gen_fmla ${PREFIX} ${SIZE} 10 0 ${SCALE} ${SEED} 16
    ./tmp/gen_log ${PREFIX} 100 ${ER} ${DELTA} ${SEED} 16
    mv ${PREFIX}.* tmp/

    if [[ "${CHECK_FLAG}" = "check" ]]
    then
        OUT=$(../bin/explanator2.exe -O ${MEASURE} -mode all -fmla tmp/${PREFIX}.mdl -log tmp/${PREFIX}.log -out_mode plain \
                                    -check 2>&1)
    else
        if [[ "${CHECK_FLAG}" = "no-check" ]]
        then
            OUT=$(../bin/explanator2.exe -O ${MEASURE} -mode all -fmla tmp/${PREFIX}.mdl -log tmp/${PREFIX}.log -out_mode plain \
                                        2>&1)
        else
            usage
        fi
    fi
    OUT_GREP=$(grep "Checker output: false\|exception" <<< "${OUT}")
    N_VERDICTS_EXPLANATOR=$(grep -c "Proof" <<< "${OUT}")
    N_VERDICTS_VERIMON=$(../../monpoly/monpoly -sig sig/ap.sig -formula tmp/${PREFIX}.mfotl -log tmp/${PREFIX}.log -verified \
                                               -nonewlastts -verbose 2>&1 | grep -c "false\|true")

    if [[ "${OUT_GREP}" == *"false"* ]]
    then
        printf "${PREFIX} ... "
        printf " !! CHECK FAILED !!\n"
    fi
    if [[ "${OUT_GREP}" == *"exception"* ]]
    then
        printf "${PREFIX} ... "
        printf " !! EXCEPTION RAISED !!\n"
    fi
    if [[ "${N_VERDICTS_EXPLANATOR}" != "${N_VERDICTS_VERIMON}" ]]
    then
        printf "${PREFIX} ... "
        printf " !! N_VERDICTS_EXPLANATOR = ${N_VERDICTS_EXPLANATOR};"
        printf " N_VERDICTS_VERIMON = ${N_VERDICTS_VERIMON} !!\n"
    fi
}

verb () {
    ./tmp/gen_fmla ${PREFIX} ${SIZE} 10 0 ${SCALE} ${SEED} 16
    ./tmp/gen_log ${PREFIX} 100 ${ER} ${DELTA} ${SEED} 16
    mv ${PREFIX}.* tmp/

    if [[ "${CHECK_FLAG}" = "check" ]]
    then
        OUT=$(../bin/explanator2.exe -O ${MEASURE} -mode all -fmla tmp/${PREFIX}.mdl -log tmp/${PREFIX}.log -out_mode plain \
                                    -check 2>&1)
    else
        if [[ "${CHECK_FLAG}" = "no-check" ]]
        then
            OUT=$(../bin/explanator2.exe -O ${MEASURE} -mode all -fmla tmp/${PREFIX}.mdl -log tmp/${PREFIX}.log -out_mode plain \
                                        2>&1)
        else
            usage
        fi
    fi
    OUT_GREP=$(grep "Checker output: false\|exception" <<< "${OUT}")
    N_VERDICTS_EXPLANATOR=$(grep -c "Proof" <<< "${OUT}")
    N_VERDICTS_VERIMON=$(../../monpoly/monpoly -sig sig/ap.sig -formula tmp/${PREFIX}.mfotl -log tmp/${PREFIX}.log -verified \
                                               -nonewlastts -verbose 2>&1 | grep -c "false\|true")

    printf "${PREFIX} ... "
    if [[ "${OUT_GREP}" == "" ]]
    then printf "OK"
    fi
    if [[ "${OUT_GREP}" == *"false"* ]]
    then
        printf " !! CHECK FAILED !!"
    fi
    if [[ "${OUT_GREP}" == *"exception"* ]]
    then
        printf " !! EXCEPTION RAISED !!"
    fi
    if [[ "${N_VERDICTS_EXPLANATOR}" != "${N_VERDICTS_VERIMON}" ]]
    then
        printf " !! N_VERDICTS_EXPLANATOR = ${N_VERDICTS_EXPLANATOR};"
        printf " N_VERDICTS_VERIMON = ${N_VERDICTS_VERIMON} !!"
    fi
    printf "\n"
}

if [ "$#" -eq 8 ]
then
    if [[ "${MODE}" == "simp" ]]
    then simp
    fi
    if [[ "${MODE}" == "verb" ]]
    then time verb
    fi
else
    usage
fi
