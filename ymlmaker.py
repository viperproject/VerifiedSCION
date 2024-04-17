#!/usr/bin/python3

import yaml
from os import path
import os
from copy import deepcopy
import re
from functools import reduce

job_template = """  verify-router-{filename}-{line}:
    runs-on: ubuntu-latest
    steps:
      - name: Checkout the VerifiedSCION repository
        uses: actions/checkout@v3
      - name: Verify package 'router/' at {file}:{line}
        uses: viperproject/gobra-action@main
        with:
          files: {files}
          timeout: 6h
          headerOnly: ${{ env.headerOnly }}
          module: ${{ env.module }}
          includePaths: ${{ env.includePaths }}
          assumeInjectivityOnInhale: ${{ env.assumeInjectivityOnInhale }}
          checkConsistency: ${{ env.checkConsistency }}
          parallelizeBranches: '1'
          # The following flag has a significant influence on the number of branches verified.
          # Without it, verification would take a lot longer.
          imageVersion: ${{ env.imageVersion }}
          mceMode: 'on'
          requireTriggers: ${{ env.requireTriggers }}
          overflow: ${{ env.overflow }}
          useZ3API: ${{ env.useZ3API }}
          disableNL: '0'
          viperBackend: ${{ env.viperBackend }}
          unsafeWildcardOptimization: '0'
"""

def format_files(files, f, l):
    if type(l) == list:
        lines = ",".join(l)
    else:
        lines = l
    return " ".join([f"router/{i}", f"router/{i}@{lines}"][f==i] for i in files)

def make_job_template(files, f, l):
    if type(l) == list:
        return job_template.replace("{file}", f).replace("{filename}", f.split(".")[0]).replace("{line}", "everywhere").replace("{files}", format_files(files, f, l))
    return job_template.replace("{file}", f).replace("{filename}", f.split(".")[0]).replace("{line}", l).replace("{files}", format_files(files, f, l))

def multi_split(l, stuff):
    if len(stuff) == 1: return l.split(stuff[0])
    return [j for i in multi_split(l, stuff[1:]) for j in i.split(stuff[0])]

def has_header(f):
    with open(f, 'r') as fhandle:
        return any(["// +gobra" in l for l in fhandle.readlines()])
    
def get_files(p):
    files = [os.path.join(p, i) for i in os.listdir(p) if re.match(r'.+(\.go|\.gobra)$', i) is not None and has_header(os.path.join(p, i))]
    return files

def get_func_lines(fname):
    inc = False
    with open(f"router/{fname}", 'r') as fhandle:
        lines = fhandle.readlines()
        for i, l in enumerate(lines):
            if "/*" in l and not "/*@" in "".join(l.split(" ")):
                inc = True
            if "*/" in l and not "@*/" in "".join(l.split(" ")):
                inc = False
            if inc:
                continue
            words = multi_split(l, [" ", ")", "(", "@"])
            if "func" in words or "outline" in words:
                yield str(i+1)

def get_files(fname, line):
    files = os.listdir("router/")

files = [f for f in os.listdir("router/") if (f.endswith(".go") or f.endswith(".gobra")) and has_header(f"router/{f}")]

with open("metagobra.yml", 'r') as fhandle:
    prefix = fhandle.read()

with open(".github/workflows/gobra.yml", 'w') as fhandle:
    fhandle.write(prefix)
    for f in files:
        if f != "dataplane.go":
            fhandle.write(make_job_template(files, f, [i for i in get_func_lines(f)]))
        else:
            for l in get_func_lines(f):
                fhandle.write(make_job_template(files, f, l))
