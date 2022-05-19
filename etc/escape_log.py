#!/usr/bin/env python3

import sys

def quit():
    print('usage: python escape_log.py file_name.log')
    exit(1)


if (len(sys.argv)) < 2:
    quit()

file_name = sys.argv[1]

try:
    log = open(file_name, 'r')
    print(log.read().__repr__())

except:
    quit()
