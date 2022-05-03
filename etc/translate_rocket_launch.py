#!/usr/bin/env python3

import sys
import csv
import math

def quit():
    print('usage: python translate_rocker_launch.py file_name.csv')
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

                accx = float(row[0])
                accy = float(row[1])
                accz = float(row[2])
                ts = row[9]

                angle = math.acos(accz/math.sqrt((accx ** 2) + (accy ** 2) + (accz ** 2))) * (180.0 / math.pi)

                if angle > 100:
                    atoms.append('a0')

                if row[10] == '1':
                    atoms.append('a1')

                if row[10] == '2':
                    atoms.append('a2')

                writer.write('@' + ts + ' ' + (' '.join(atoms)) + '\n')

except:
    quit()
