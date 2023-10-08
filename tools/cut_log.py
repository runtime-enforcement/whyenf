#!/usr/bin/env python3

import sys

def quit():
    print('usage: python cut_log.py {file name}.log {out file name}.log {start line} {end line}')
    exit(1)


if (len(sys.argv)) < 5:
    quit()

file_name = sys.argv[1]
out_file_name = sys.argv[2]
start_line = int(sys.argv[3])
end_line = int(sys.argv[4])

lineNumber = 0

try:
    with open(file_name) as infile:
        with open(out_file_name, 'w') as outfile:

            for line in infile:

                if lineNumber >= start_line and lineNumber <= end_line:
                    outfile.write(line)

                lineNumber += 1

except:
    quit()
