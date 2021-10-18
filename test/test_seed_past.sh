#!/bin/bash

# ./test_seed 10 2 size 0
# parallel ./test_seed.sh 10 2 size ::: {0..100}

SIZE=$1
ER=$2
MEASURE=$3
SEED=$4
PREFIX="TMP_${SIZE}_${ER}_${SEED}"

./gen_fmla ${PREFIX} ${SIZE} 50 2 1 ${SEED} 16
./gen_log ${PREFIX} 100 ${ER} 4 ${SEED} 16
OUT=$(../explanator2.native -O ${MEASURE} -mode all -debug -fmla ${PREFIX}.mdl -log ${PREFIX}.log 2>1 | grep "Checker output")
echo -n "${PREFIX} ... "
if [[ "${OUT}" == "" ]]
        then echo "PASSED"
fi
if [[ "${OUT}" != "" ]]
        then echo "FAILED"
fi
