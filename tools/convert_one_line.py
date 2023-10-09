#!/usr/bin/env python3

import sys

def quit():
    print('usage: python convert_one_line.py {file name}.log {out file name}.log')
    exit(1)


if (len(sys.argv)) < 3:
    quit()

file_name = sys.argv[1]
out_file_name = sys.argv[2]

try:
    with open(file_name) as infile:
        with open(out_file_name, 'w') as outfile:

            for line in infile:

                outfile.write(line.rstrip('\n') + "\\n")

except:
    quit()
