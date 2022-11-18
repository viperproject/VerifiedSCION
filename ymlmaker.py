#!/usr/bin/python3

import yaml
from os import path
import os
from copy import deepcopy
import re
from functools import reduce

f = "metagobra.yml"
ftarget = ".github/workflows/gobra.yml"

def get_file(s):
    if "@" in s:
        return s[:s.index("@")]
    return s

def partition(s):
    fname = s[:s.index("@")]
    rest = s[s.index("@")+1:].split(",")
    f1 = fname + "@"
    f2 = fname + "@"
    for i in range(len(rest)):
        if len(f1) + len(rest[i]) + 1 < 250:
            if f1[-1] != "@":
                f1 += f",{rest[i]}"
            else:
                f1 += str(rest[i])
            continue
        f2 += ",".join(rest[i:])
        break
    return f1, f2

def normalize(yml):
    if "files" in yml['with'].keys():
        ret = []
        files = yml['with']['files'].split()
        large_files = [i for i in files if len(i) > 250]
        rest_files = [i for i in files if len(i) <= 250]
        for i in range(len(large_files)):
            while len(large_files[i]) > 250:
                f1, f2 = partition(large_files[i])
                toappend = deepcopy(yml)
                toappend['with']['files'] = f' {f1} {" ".join(get_file(e) for j, e in enumerate(large_files) if j != i)} {" ".join(get_file(e) for e in rest_files)}'
                toappend['name'] += str(len(ret))
                ret.append(toappend)
                large_files[i] = f2
        toappend = deepcopy(yml)
        toappend['with']['files'] = f' {" ".join(large_files)} {" ".join(rest_files)}'
        ret.append(toappend)
        return ret
    return [yml]
    
def has_header(f):
    with open(f, 'r') as fhandle:
        return any(["// +gobra" in l for l in fhandle.readlines()])
    
def get_files(p):
    files = [os.path.join(p, i) for i in os.listdir(p) if re.match(r'.+(\.go|\.gobra)$', i) is not None and has_header(os.path.join(p, i))]
    return files

def parse_args(line):
    if m := re.match(r'\s*// \$!\[\s*(.*)\s*\]!\$', line):
        args = m.group(1)
        if "disableMoreCompleteExhale" in args and "parallelizeBranches" in args:
            return "both"
        elif "disableMoreCompleteExhale" in args:
            return "dis"
        elif "parallelizeBranches" in args:
            return "par"
    return "none"

def get_func_lines_annos(fname):
    with open(fname, 'r') as fhandle:
        lines = fhandle.readlines()
        funcs = {'dis': [], 'par': [], 'both': [], 'none': []}
        for l, e in enumerate(lines):
            if "func" in e or "outline" in e:
                funcs[parse_args(lines[l-1])].append(l+1)
        return funcs

def alter_entry(entry: dict):
    ret = deepcopy(entry)
    if (int(ret['with'].get('disect', 0)) == 1):
        ret['with'].pop('disect')
        directory = ret['with'].pop('packages')
        files = get_files(directory)
        retdict = {"dis": deepcopy(ret), "par": deepcopy(ret), "both": deepcopy(ret), "none": ret}
        enabled = {"dis": False, "par": False, "both": False, "none": False}
        for key in ['dis', 'par', 'both', 'none']:
            retdict[key]['name'] += '-'+key
            retdict[key]['with']['files'] = ""
        retdict['dis']['with']['disableMoreCompleteExhale'] = 1
        retdict['both']['with']['disableMoreCompleteExhale'] = 1
        retdict['par']['with']['parallelizeBranches'] = 1
        retdict['both']['with']['parallelizeBranches'] = 1
        for f in files:
            for key, lines in get_func_lines_annos(f).items():
                if len(lines) > 0:
                    enabled[key] = True
                    retdict[key]['with']['files'] += f' {f}@{",".join(str(j) for j in lines)}'
                else:
                    retdict[key]['with']['files'] += f' {f}'
        return reduce(lambda a, b: a + b, [normalize(v) for k, v in retdict.items() if enabled[k]])
    return [ret]

def split_to_many(yml):
    ret = []
    for i in yml['jobs']['verify']['steps'][2:-1]:
        toappend = deepcopy(yml)
        start = toappend['jobs']['verify']['steps'][:2]
        end = toappend['jobs']['verify']['steps'][-1]
        toappend['jobs']['verify']['steps'] = start + [deepcopy(i)] + [end]
        ret.append(toappend)
    return ret

def write_result(yml, ftarget):
    with open(ftarget, 'w') as fhandle2:
        fhandle2.write("# This Source Code Form is subject to the terms of the Mozilla Public\n# License, v. 2.0. If a copy of the MPL was not distributed with this\n# file, You can obtain one at http://mozilla.org/MPL/2.0/.\n#\n# Copyright (c) 2011-2020 ETH Zurich.\n\nname: Verify the specified codebase\n\n")
        fhandle2.write("on:\n  pull_request: # verify on pull request\n  push:\n    branches:\n    - master\n\n")
        s = yaml.dump(yml, Dumper=yaml.CDumper)
        for i in re.findall(r"files: '[^']*'", s):
            s = s.replace(i, " ".join(i.replace("\n", "").split()))
        fhandle2.write(s)

if __name__ == "__main__":
    with open(f, 'r') as fhandle:
        yml = yaml.load(fhandle, Loader=yaml.CLoader)
        distinct = yml['jobs']['verify']['steps']
        newdistinct = []
        newdistinct.extend(distinct[:3])
        for i in distinct[3:-1]:
            newdistinct.extend(alter_entry(i))
        newdistinct.append(distinct[-1])
        yml['jobs']['verify']['steps'] = newdistinct
        yml.pop(True)
        yml.pop('name')
        ymls = split_to_many(yml)
        for i, e in enumerate(ymls):
            write_result(e, f'{ftarget[:-4]}{i}.yml')

