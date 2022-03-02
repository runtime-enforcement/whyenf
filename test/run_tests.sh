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

if ! [[ "${N_SEEDS}" =~ ^[0-9]+$ ]] || [[ "${MEASURE}" != "size" ]]
then
    printf "usage: run_tests.sh [n_seeds] [measure]\n"
    exit 1
fi

# Arrays:
SIZES=(10 20)
SCALES=(1 5 10)
ERS=(1 10 20)
DELTAS=(4 20)
SEEDS=$(seq 0 "${N_SEEDS}")

for i in "${SIZES[@]}"; do
    for j in "${SCALES[@]}"; do
        for k in "${ERS[@]}"; do
            for l in "${DELTAS[@]}"; do
                printf "<@> Running set of tests with parameters\n"
                printf "<@> { size = $i | scale = $j | er = $k | delta = $l }\n"
                parallel ./test_seed.sh simp $i $j $k $l "${MEASURE}" ::: "${SEEDS}"
                printf "\n"
            done
        done
    done
done

./clean.sh
