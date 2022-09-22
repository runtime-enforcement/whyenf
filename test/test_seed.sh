#!/bin/bash

# ./test_seed.sh no-check verb 10 1 1 4 size 144

# Input parameters:
MODE=$3
SIZE=$4
SCALE=$5
ER=$6
DELTA=$7
MEASURE=$8
OPERATORS=$9
SEED=$10

# Flags:
CHECK_FLAG=$1
WEIGHT_FLAG=$2

# Variables:
PREFIX="TMP_${SIZE}_${SCALE}_${ER}_${DELTA}_${MEASURE}_${SEED}"
OUT=""

usage () {
    printf "usage: test_seed.sh [check or no-check] [weight or no-weight] [mode] [size] [scale] [er] [delta] [measure] [mtl or extended-mtl] [seed]\n"
    exit 1
}

simp () {
    if [[ "${OPERATORS}" = "mtl" ]]
    then
        ./tmp/gen_fmla ${PREFIX} ${SIZE} 10 0 ${SCALE} ${SEED} 16
    else
        ./tmp/gen_fmla_full ${PREFIX} ${SIZE} 10 0 ${SCALE} ${SEED} 16
    fi

    ./tmp/gen_log ${PREFIX} 100 ${ER} ${DELTA} ${SEED} 16
    mv ${PREFIX}.* tmp/

    if [[ "${CHECK_FLAG}" = "check" ]]
    then
        if [[ "${WEIGHT_FLAG}" = "weight" ]]
        then
            OUT=$(../bin/explanator2.exe -O ${MEASURE} -mode all -fmla tmp/${PREFIX}.mdl -log tmp/${PREFIX}.log \
                                         -check -out_mode plain -weights test_weights.ws 2>&1)
        else
            OUT=$(../bin/explanator2.exe -O ${MEASURE} -mode all -fmla tmp/${PREFIX}.mdl -log tmp/${PREFIX}.log -out_mode plain \
                                         -check 2>&1)
        fi
    else
        if [[ "${CHECK_FLAG}" = "no-check" ]]
        then
            if [[ "${WEIGHT_FLAG}" = "weight" ]]
            then
                OUT=$(../bin/explanator2.exe -O ${MEASURE} -mode all -fmla tmp/${PREFIX}.mdl -log tmp/${PREFIX}.log \
                                             -out_mode plain -weights test_weights.ws 2>&1)
            else
                OUT=$(../bin/explanator2.exe -O ${MEASURE} -mode all -fmla tmp/${PREFIX}.mdl -log tmp/${PREFIX}.log -out_mode plain \
                                              2>&1)
            fi
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
    if [[ "${OPERATORS}" = "mtl" ]]
    then
        if [[ "${N_VERDICTS_EXPLANATOR}" != "${N_VERDICTS_VERIMON}" ]]
        then
            printf "${PREFIX} ... "
            printf " !! N_VERDICTS_EXPLANATOR = ${N_VERDICTS_EXPLANATOR};"
            printf " N_VERDICTS_VERIMON = ${N_VERDICTS_VERIMON} !!\n"
        fi
    fi
}

verb () {
    if [[ "${OPERATORS}" = "mtl" ]]
    then
        ./tmp/gen_fmla ${PREFIX} ${SIZE} 10 0 ${SCALE} ${SEED} 16
    else
        ./tmp/gen_fmla_full ${PREFIX} ${SIZE} 10 0 ${SCALE} ${SEED} 16
    fi

    ./tmp/gen_log ${PREFIX} 100 ${ER} ${DELTA} ${SEED} 16
    mv ${PREFIX}.* tmp/

    if [[ "${CHECK_FLAG}" = "check" ]]
    then
        if [[ "${WEIGHT_FLAG}" = "weight" ]]
        then
            OUT=$(../bin/explanator2.exe -O ${MEASURE} -mode all -fmla tmp/${PREFIX}.mdl -log tmp/${PREFIX}.log \
                                         -check -out_mode plain -weights test_weights.ws 2>&1)
        else
            OUT=$(../bin/explanator2.exe -O ${MEASURE} -mode all -fmla tmp/${PREFIX}.mdl -log tmp/${PREFIX}.log -out_mode plain \
                                         -check 2>&1)
        fi
    else
        if [[ "${CHECK_FLAG}" = "no-check" ]]
        then
            if [[ "${WEIGHT_FLAG}" = "weight" ]]
            then
                OUT=$(../bin/explanator2.exe -O ${MEASURE} -mode all -fmla tmp/${PREFIX}.mdl -log tmp/${PREFIX}.log \
                                             -out_mode plain -weights test_weights.ws 2>&1)
            else
                OUT=$(../bin/explanator2.exe -O ${MEASURE} -mode all -fmla tmp/${PREFIX}.mdl -log tmp/${PREFIX}.log -out_mode plain \
                                              2>&1)
            fi
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
    if [[ "${OPERATORS}" = "mtl" ]]
    then
        if [[ "${N_VERDICTS_EXPLANATOR}" != "${N_VERDICTS_VERIMON}" ]]
        then
            printf "${PREFIX} ... "
            printf " !! N_VERDICTS_EXPLANATOR = ${N_VERDICTS_EXPLANATOR};"
            printf " N_VERDICTS_VERIMON = ${N_VERDICTS_VERIMON} !!\n"
        fi
    fi
    printf "\n"
}

if [ "$#" -eq 10 ]
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
