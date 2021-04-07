#!/usr/bin/env python3

import sys
import subprocess
import os
import argparse
import json

input_dir_root = "test/test-sources/"
output_dir_root = "test/test-outputs/"

subdirs = ["odefa-basic", "odefa-types", "natodefa-basic", "natodefa-types"]

def run_test():
    for subdir in subdirs:
        indir = os.path.join(input_dir_root, subdir)
        outdir = os.path.join(output_dir_root, subdir)
        if not os.path.isdir(outdir):
            os.mkdir(outdir)
        for in_filename in os.scandir(indir):
            # Name of out file
            pre, ext = os.path.splitext(os.path.basename(in_filename))
            out_filename = os.path.join(outdir, pre + ".json")
            # Run sato
            args = ["./sato", "-fjson", "-s10000", in_filename]
            result = subprocess.run(args, stdout=subprocess.PIPE)
            result_str = result.stdout.decode("utf-8")
            outfile = open(out_filename, 'w')
            outfile.write(result_str)
            outfile.close()
            print("Create test for " + pre)

def main():
    run_test()

if __name__ == '__main__':
    main()
