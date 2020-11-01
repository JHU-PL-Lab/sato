#!/usr/bin/env python3

import sys
import subprocess
import os
import argparse
import json

input_dir = "test/test-sources/natodefa-types/"
output_dir = "test/test-outputs/natodefa-types/"

def run_test():
    for current_dir, dirs, files in os.walk(input_dir):
        for filename in files:
            # Name of out file
            pre, ext = os.path.splitext(filename)
            out_filename = os.path.join(output_dir, pre + ".out")
            # Run sato
            args = ["./type_checker", "-m10000", os.path.join(current_dir, filename)]
            result = subprocess.run(args, stdout=subprocess.PIPE)
            result_str = result.stdout.decode("utf-8")
            if not os.path.exists(os.path.join(output_dir, current_dir)):
                os.makedirs(os.path.join(output_dir, current_dir))
            with open(out_filename, 'w') as outfile:
                outfile.write(result_str)
                outfile.close()
            print("Create test for " + filename)

def main():
    run_test()

if __name__ == '__main__':
    main()
