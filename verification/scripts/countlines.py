"""
The program counts and reports lines of code and lines of annotation for VerifiedScion.
Currently a line is considered to be a line of code if all of these hold:
- It is inside a '.go' file with the header // +gobra
- It is not just whitespace
- It is not a single line comment
A line of annotation is a line for which either holds:
- It is inside a '.gobra' file with the header // +gobra and is not a single line comment or blank
- It is inside a '.go' file with the header // +gobra and starts with (possibly whitespace) and
  '// @' or '//@'

Current limitations:
- The program does not count inlining of ghost code in lines
- Multi line comments might increase the lines of code in .go files and lines of annotation in
  .gobra files
"""

import os
from os import path
import re


def has_header(fname):
    with open(fname, 'r') as fhandle:
        for line in fhandle:
            if line.startswith("package"):
                return False
            if "+gobra" in line:
                return True
    return None


def handle_go_file(fname):
    loc = 0
    loa = 0
    with open(fname, 'r') as fhandle:
        for line in fhandle:
            if re.match(r'\s*// ?@.*', line):
                loa += 1
            elif (len(line.strip()) > 0) and not (re.match(r'\s*//.*', line)):
                loc += 1
    return loc, loa


def handle_gobra_file(fname):
    loa = 0
    with open(fname, 'r') as fhandle:
        for line in fhandle:
            if (len(line.strip()) > 0) and not (re.match(r'\s*//.*', line)):
                loa += 1
    return loa


loc = 0  # lines of code
loa = 0  # lines of annotation

for dirname, dirs, files in os.walk('../../', topdown=True):
    # exclude dotted directories
    dirs[:] = [d for d in dirs if (not path.split(d)[-1].startswith('.'))]
    tocheck = [
        path.join(dirname, f) for f in files
        if (f.endswith(".go") or f.endswith(".gobra"))
        and has_header(path.join(dirname, f))
    ]
    if len(tocheck) > 0:
        for f in tocheck:
            if f.endswith(".go"):
                new_loc, new_loa = handle_go_file(f)
            else:
                new_loc = 0
                new_loa = handle_gobra_file(f)
            loc += new_loc
            loa += new_loa

print(f"Lines of Code: {loc}")
print(f"Lines of Annotation: {loa}")
