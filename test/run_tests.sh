#!/bin/bash

## * gen_fmla
##
## PREFIX | SIZE | MAXR | TYPE | SCALE | SEED | APS
##                  10     0                    16
##
## * gen_log
## PREFIX | TS_CNT | ER | DELTA | SEED | APS
##           100                         16
##
## * possible combinations
## SIZE  -> 10 100
## SCALE -> 1  5   10
## ER    -> 1  10  100
## DELTA -> 4  100

# Input parameters:
N_SEEDS=$1
MEASURE=$2

# Flags:
CHECK_FLAG=$3
WEIGHT_FLAG=$4

usage () {
    printf "usage: run_tests.sh [n_seeds] [measure] [check or no-check] [weight or no-weight]\n"
    exit 1
}

if ! [[ "${N_SEEDS}" =~ ^[0-9]+$ ]] || [[ "${MEASURE}" != "size" ]] || ! [ "$#" -eq 4 ]
then
    usage
fi

# Arrays:
# SIZES=(10 20)
# SCALES=(1 5 10)
# ERS=(1 5 10)
# DELTAS=(4 8 12)
SIZES=(3 4 5 6 7 8 9 10)
SCALES=(1 5)
ERS=(1 5)
DELTAS=(4)
SEEDS=$(seq 0 "${N_SEEDS}")

for i in "${SIZES[@]}"; do
    for j in "${SCALES[@]}"; do
        for k in "${ERS[@]}"; do
            for l in "${DELTAS[@]}"; do
                if [[ "${CHECK_FLAG}" == "check" ]]
                then
                    printf "<@> Running ${N_SEEDS} verified tests with parameters\n"
                    printf "<@> { size = $i | scale = $j | er = $k | delta = $l }\n"

                    if [[ "${WEIGHT_FLAG}" == "weight" ]]
                    then
                        printf "<@> Loading random weights... Done.\n"
                        time parallel ./test_seed.sh check weight simp $i $j $k $l "${MEASURE}" ::: "${SEEDS}"
                    else
                        time parallel ./test_seed.sh check no-weight simp $i $j $k $l "${MEASURE}" ::: "${SEEDS}"
                    fi

                    ./clean.sh
                    printf "\n"
                else
                    if [[ "${CHECK_FLAG}" == "no-check" ]]
                    then
                        printf "<@> Running ${N_SEEDS} tests with parameters\n"
                        printf "<@> { size = $i | scale = $j | er = $k | delta = $l }\n"

                        if [[ "${WEIGHT_FLAG}" == "weight" ]]
                        then
                            printf "<@> Loading random weights... Done.\n"
                            time parallel ./test_seed.sh no-check weight simp $i $j $k $l "${MEASURE}" ::: "${SEEDS}"
                        else
                            time parallel ./test_seed.sh no-check no-weight simp $i $j $k $l "${MEASURE}" ::: "${SEEDS}"
                        fi

                        ./clean.sh
                        printf "\n"
                    else
                        usage
                    fi
                fi
            done
        done
    done
done
