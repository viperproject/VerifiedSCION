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

def key_arguments(key):
    args = ""
    if key in ["dis", "both"]:
        args += "--disableMoreCompleteExhale "
    if key in ["par", "both"]:
        args += "--parallelizeBranches"
    if len(args) == 0:
        args = "no extra args"
    return args

def normalize(key, yml, dirname):
    if "files" in yml['with'].keys():
        ret = []
        files = yml['with']['files'].split()
        large_files = [i for i in files if len(i) > 250]
        rest_files = [i for i in files if len(i) <= 250]
        i = -1
        for i in range(len(large_files)):
            while len(large_files[i]) > 250:
                f1, f2 = partition(large_files[i])
                toappend = deepcopy(yml)
                toappend['with']['files'] = f' {f1} {" ".join(get_file(e) for j, e in enumerate(large_files) if j != i)} {" ".join(get_file(e) for e in rest_files)}'
                toappend['name'] += str(len(ret))
                toappend['with']['tempname'] = f"Verifying functions in {dirname} with {key_arguments(key)} part {i}"
                ret.append(toappend)
                large_files[i] = f2
        toappend = deepcopy(yml)
        toappend['with']['files'] = f' {" ".join(large_files)} {" ".join(rest_files)}'
        toappend['with']['tempname'] = f"Verifying functions in {dirname} with {key_arguments(key)} part {i+1}"
        ret.append(toappend)
        return ret
    ret = deepcopy(yml)
    ret['with']['tempname'] = f"Verifying functions in {dirname} with {key_arguments(key)}"
    return [ret]
    
def has_header(f):
    with open(f, 'r') as fhandle:
        return any(["// +gobra" in l for l in fhandle.readlines()])
    
def get_files(p):
    files = [os.path.join(p, i) for i in os.listdir(p) if re.match(r'.+(\.go|\.gobra)$', i) is not None and has_header(os.path.join(p, i))]
    return files

def parse_args(line, loc):
    iso = False
    if m := re.match(r'\s*// \$!\[\s*(.*)\s*\]!\$', line):
        args = [i.strip() for i in m.group(1).split()]
        for i in args:
            if i not in ["disableMoreCompleteExhale", "parallelizeBranches", "isolate", "closure"]:
                print(f"Warning: <{loc}>: unrecognised flag '{i}'")
        if "closure" in args:
            return None, None
        iso = "isolate" in args
        if "disableMoreCompleteExhale" in args and "parallelizeBranches" in args:
            return "both", iso
        elif "disableMoreCompleteExhale" in args:
            return "dis", iso
        elif "parallelizeBranches" in args:
            return "par", iso
    return "none", iso

def get_func_lines_annos(fname):
    with open(fname, 'r') as fhandle:
        lines = fhandle.readlines()
        funcs = {'dis': [], 'par': [], 'both': [], 'none': [], 'isolated': []}
        for l, e in enumerate(lines):
            if "func" in e or "outline" in e:
                args, iso = parse_args(lines[l-1], f'{fname}:{l-1}')
                if args is None:
                    continue
                if iso:
                    if "func" in e:
                        match = re.match(r'\s*func\s*((\([^\)]+\)\s*([^\(\s]*)\s*\(.*)|(\s*([^\(\s]*)\s*\(.*))', e.replace("/*@", "").replace("@*/", ""))
                        name = {"{fname}:{match.groups()[2] or match.groups()[4]}"}
                    else:
                        name = f"outline at {fname}@{l}"
                    funcs['isolated'].append((l+1, args, name))
                else:
                    funcs[args].append(l+1)
        return funcs

def alter_entry(entry: dict):
    ret = deepcopy(entry)
    if (int(ret['with'].get('disect', 0)) == 1):
        ret['with'].pop('disect')
        directory = ret['with'].pop('packages')
        files = get_files(directory)
        retdict = {"dis": deepcopy(ret), "par": deepcopy(ret), "both": deepcopy(ret), "none": ret}
        isolated = []
        enabled = {"dis": False, "par": False, "both": False, "none": False}
        for key in ['dis', 'par', 'both', 'none']:
            retdict[key]['name'] += '-'+key
            retdict[key]['with']['files'] = ""
        retdict['dis']['with']['disableMoreCompleteExhale'] = 1
        retdict['both']['with']['disableMoreCompleteExhale'] = 1
        retdict['par']['with']['parallelizeBranches'] = 1
        retdict['both']['with']['parallelizeBranches'] = 1
        for f in files:
            line_annos = get_func_lines_annos(f)
            isolated.extend((f'{f}@{line}', args, name) for line, args, name in line_annos.pop('isolated'))
            for key, lines in line_annos.items():
                if len(lines) > 0:
                    enabled[key] = True
                    retdict[key]['with']['files'] += f' {f}@{",".join(str(j) for j in lines)}'
                else:
                    retdict[key]['with']['files'] += f' {f}'
        retisolated = []
        for f, args, name in isolated:
            toappend = deepcopy(entry)
            toappend['with'].pop('disect')
            toappend['with'].pop('packages')
            if args in ('dis', 'both'):
                toappend['with']['disableMoreCompleteExhale'] = 1
            if args in ('par', 'both'):
                toappend['with']['parallelizeBranches'] = 1
            toappend['with']['files'] = f' {f} {" ".join(fil for fil in files if fil not in f)}'
            toappend['with']['tempname'] = f"Verifying function {name}"
            retisolated.append(toappend)
        return retisolated + reduce(lambda a, b: a + b, (normalize(k, v, directory) for k, v in retdict.items() if enabled[k]))
    ret['with']['tempname'] = f"Verifying package {ret['with']['packages']}"
    return [ret]

def split_to_many(yml):
    ret = []
    yml['jobs']['verify']['steps'][2]['with']['tempname'] = "Verifying the verification directory"
    for i in yml['jobs']['verify']['steps'][2:-1]:
        toappend = deepcopy(yml)
        start = toappend['jobs']['verify']['steps'][:2]
        end = toappend['jobs']['verify']['steps'][-1]
        # If we want stats we just uncomment the + [end] part
        toappend['jobs']['verify']['steps'] = start + [deepcopy(i)]# + [end]
        name = toappend['jobs']['verify']['steps'][2]['with'].pop('tempname')
        ret.append((toappend, name))
    return ret

def write_result(data, ftarget):
    yml, name = data
    with open(ftarget, 'w') as fhandle2:
        fhandle2.write("# This Source Code Form is subject to the terms of the Mozilla Public\n# License, v. 2.0. If a copy of the MPL was not distributed with this\n# file, You can obtain one at http://mozilla.org/MPL/2.0/.\n#\n# Copyright (c) 2011-2020 ETH Zurich.\n\n")
        fhandle2.write(f"name: {name}\n\n")
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

