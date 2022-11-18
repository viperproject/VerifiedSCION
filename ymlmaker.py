#!/usr/bin/python3

import yaml
from os import path
import os
from copy import deepcopy
import re

f = "metagobra.yml"
ftarget = ".github/workflows/gobra.yml"

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
                    retdict[key]['with']['files'] += f' {path.join(directory,f)}'
        return [v for k, v in retdict.items() if enabled[k]]
    return [ret]

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
        with open(ftarget, 'w') as fhandle2:
            fhandle2.write("# This Source Code Form is subject to the terms of the Mozilla Public\n# License, v. 2.0. If a copy of the MPL was not distributed with this\n# file, You can obtain one at http://mozilla.org/MPL/2.0/.\n#\n# Copyright (c) 2011-2020 ETH Zurich.\n\nname: Verify the specified codebase\n\n")
            fhandle2.write("on:\n  pull_request: # verify on pull request\n  push:\n    branches:\n    - master\n\n")
            s = yaml.dump(yml, Dumper=yaml.CDumper)
            for i in re.findall(r"files: '[^']*'", s):
                s = s.replace(i, " ".join(i.replace("\n", "").split()))
            fhandle2.write(s)
