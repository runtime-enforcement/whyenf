#!/usr/bin/env python3

import sys
import csv
import math

def quit():
    print('usage: python convert_dejavu.py file_name.csv')
    exit(1)


if (len(sys.argv)) < 2:
    quit()

file_name = sys.argv[1]
out_file_name = file_name.split('.')[0] + '.log'

try:
    with open(file_name) as csvfile:
        with open(out_file_name, 'w') as writer:

            reader = csv.reader(csvfile, delimiter=',')

            ts = 0

            for row in reader:

                pred = row[0]
                val1 = row[1]
                val2 = row[2]

                writer.write('@' + str(ts) + ' ' + pred + '(' + val1 + ',' + val2 + ')\n')

                ts += 1

except:
    quit()
