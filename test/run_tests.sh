#!/bin/bash

MEASURE="size"

for file in "../examples"/*
do
    if [[ $file = *.mtl ]]; then
        echo "Processing ${file%.*}"
        file_without_ext="${file%.*}" # file name without extension
        f="${file_without_ext##*/}"   # file name without path
        ./aerial.native -mtl -fmla "$file" -log "${file_without_ext}.log" -out "output/${f}.out.aerial"
        ../explanator2.native -O "$MEASURE" -mode bool -fmla "$file" -log "${file_without_ext}.log" -out "output/${f}.out.explanator2"
        d=$(diff "output/${f}.out.aerial" "output/${f}.out.explanator2")
        if [ -z "$d" ]; then
            echo "OK"
        else
            echo "Diff: ${d}"
        fi
    fi
done

echo "Cleaning output files..."
for file in "output"/*
do
    rm -v "$file"
done


