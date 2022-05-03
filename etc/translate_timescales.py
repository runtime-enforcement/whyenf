#!/usr/bin/env python3

import sys
import csv

def quit():
    print('usage: python translate_timescales.py file_name.csv')
    exit(1)


if (len(sys.argv)) < 2:
    quit()

file_name = sys.argv[1]
out_file_name = file_name.split('.')[0] + '.log'

try:
    with open(file_name) as csvfile:
        with open(out_file_name, 'w') as writer:

            reader = csv.reader(csvfile, delimiter=',')
            header = next(reader)

            for row in reader:
                atoms = []

                for i in range(1, len(header)):
                    if row[i] == '1':
                        atoms.append(header[i])

                writer.write('@' + row[0] + ' ' + (' '.join(atoms)) + '\n')
except:
    quit()
