#!/usr/bin/env python3

import sys
import random

def quit():
    print('usage: python generate_weights.py file_name.ws')
    exit(1)


if (len(sys.argv)) < 2:
    quit()

file_name = sys.argv[1]

try:
    with open(file_name, 'w') as f:
        suffix = ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H']
        for s in suffix:
            f.write("a" + s + ": " + str(random.randrange(200)) + "\n")

except:
    quit()
