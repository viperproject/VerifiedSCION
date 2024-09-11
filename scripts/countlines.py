#!/usr/bin/env python3

import re
import sys
import os
from collections import defaultdict
import pandas as pd


def replace_comments(l):
    for c in ["/*", "//", "/*@", "/* @", "*/", "@*/", "@ */"]:
        l = l.replace(c, "")
    return l.strip()


def file_lines_go(fname):
    loc = 0  # lines of code
    los = 0  # lines of specification
    hyb = 0  # hybrid lines
    braces = 0
    verified = 0
    ignored = 0
    abstract = 0
    trustedfuncs = 0
    total = 0
    inc = False
    t = None
    interface = False
    requiresfalse = False
    trusted = False
    override = False
    specuntil = -1
    bodyuntil = -1
    with open(fname, "r") as fhandle:
        lines = fhandle.readlines()
        for i, l in enumerate(lines):
            if braces < 0:
                print(lines[i-1])
                print("DANGER")
            if i >= bodyuntil:
                trusted = False
                requiresfalse = False
                override = False
            if ("/*@" in l or "/* @" in l) and ("@*/" in l or "@ */" in l):
                if "func" in [j.strip() for i in l.split(" ") for j in i.split("(")]:
                    fverified, fignored, fabstract, ftrusted = calculate_func_stuff(i, lines, trusted, requiresfalse, override)
                    verified += fverified
                    ignored += fignored
                    abstract += fabstract
                    trustedfuncs += ftrusted
                if len(replace_comments(l)) != 0:
                    hyb += 1
                    loc += 1
                    los += 1
                braces += get_amount(l)
            else:
                if (t1 := "/*@" in l or "/* @" in l) or "/*" in l:
                    inc = True
                    t = int(t1)
                # match lines starting with whitespace and then having "// @"
                if inc:
                    los += t
                elif re.match(r"^\s*//\s*@.*", l):
                    if "trusted" in [
                        j.strip() for i in l.split(" ") for j in i.split("(")
                    ]:
                        trusted = True
                        specuntil, bodyuntil, _ = get_spec_body(i, lines)
                    elif "requiresfalse" in "".join(i.strip() for i in l.split(" ")) or "requiresUncallable()" in "".join(i.strip() for i in l.split(" ")):
                        requiresfalse = True
                        specuntil, bodyuntil, _ = get_spec_body(i, lines)
                    los += 1
                elif re.match(r"^\s*//\s*.*", l):
                    if "::OVERRIDE::" in l:
                        override = True
                    if "::INTERFACE::" in l:
                        interface = True
                    if "::ENDOFINTERFACE::" in l:
                        interface = False
                    pass  # skip comment lines
                elif len(l.strip()) > 0:
                    if "func" in [j.strip() for i in l.split(" ") for j in i.split("(")]:
                        total += 1
                        fverified, fignored, fabstract, ftrusted = calculate_func_stuff(i, lines, trusted, requiresfalse, override)
                        verified += fverified
                        ignored += fignored
                        abstract += fabstract
                        trustedfuncs += ftrusted
                    braces += get_amount(l)
                    loc += 1
                if "@*/" in l or "@ */" in l or "*/" in l:
                    inc = False
    return loc, los, hyb, verified, ignored, abstract, trustedfuncs, 0, 0, 0, 0, total


def file_lines_gobra(fname):
    """All code lines that are not in multiline comments are counted as specification lines"""
    los = 0  # lines of specification
    verified = 0 # number of functions verified
    ignored = 0 # number of ignored functions
    abstract = 0 # number of abstract functions
    trustedfuncs = 0 # number of trusted functions
    override = False
    inc = False
    interface = False
    requiresfalse = False
    trusted = False
    specuntil = -1
    bodyuntil = -1
    with open(fname, "r") as fhandle:
        lines = fhandle.readlines()
        for i, l in enumerate(lines):
            if i >= bodyuntil:
                trusted = False
                requiresfalse = False
                override = False
            if "/*" in l:
                inc = True
            if inc:
                pass
            elif re.match(r"^\s*//\s*.*", l):
                if "::OVERRIDE::" in l:
                    override = True
                if "::INTERFACE::" in l:
                    interface = True
                if "::ENDOFINTERFACE::" in l:
                    interface = False
                pass  # skip comment lines
            elif len(l.strip()) > 0 and not inc and not interface:
                if "func" in [j.strip() for i in l.split(" ") for j in i.split("(")]:
                    fverified, fignored, fabstract, ftrusted = calculate_func_stuff(i, lines, trusted, requiresfalse, override)
                    verified += fverified
                    ignored += fignored
                    abstract += fabstract
                    trustedfuncs += ftrusted
                if "trusted" in [j.strip() for i in l.split(" ") for j in i.split("(")]:
                    trusted = True
                    specuntil, bodyuntil, _ = get_spec_body(i, lines)
                elif "requiresfalse" in "".join(i.strip() for i in l.split(" ")) or "requiresUncallable()" in "".join(i.strip() for i in l.split(" ")):
                    requiresfalse = True
                    specuntil, bodyuntil, _ = get_spec_body(i, lines)
                los += 1
            if "*/" in l:
                inc = False
    return 0, los, 0, 0, 0, 0, 0, verified, ignored, abstract, trustedfuncs, 0


def get_spec_body(i, lines):
    infunc = False
    amount = 0
    spec = -1
    for j, l in enumerate(lines[i:]):
        if (
            "func" in [j.strip() for i in l.split(" ") for j in i.split("(")]
            and spec < 0
        ):
            spec = j
        if not infunc and l.strip() == "":
            return i + spec, i + j, True
        amount += get_amount(l)
        if amount > 0 and not infunc:
            infunc = True
        if amount == 0 and infunc:
            return i + spec, i + j + 1, False
    return i + spec, len(lines), True


def calculate_func_stuff(i, lines, trusted, requiresfalse, override):
    spec, body, abstract = get_spec_body(i, lines)
    if abstract:
        # print(i, "abstract")
        return 0, 0, 1, 0
    if requiresfalse:
        # print(i, "ignored")
        return 0, 1, 0, 0
    if trusted and not override:
        # print(i, "trusted")
        return 0, 0, 0, 1
    # print(i, "verified")
    return 1, 0, 0, 0


def get_amount(l):
    opening = len(l) - len(l.replace("{", ""))
    closing = len(l) - len(l.replace("}", ""))
    return opening - closing


def file_lines(fname):
    if fname.endswith(".go"):
        return file_lines_go(fname)
    elif fname.endswith(".gobra"):
        return file_lines_gobra(fname)
    return 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0


def should_check(f):
    if not (f.endswith(".go") or f.endswith(".gobra")):
        return "", False
    res = False
    with open(f, "r") as fhandle:
        for l in fhandle:
            if re.match(r"^// \+gobra.*", l):
                res = True
            if l.startswith("package"):
                return l.split(" ")[1].strip(), res
    return "", False


def measure_lines(d, test_files, file_to_save):
    loc, los, hyb = defaultdict(int), defaultdict(int), defaultdict(int)
    verified, ignored, abstract, trusted = defaultdict(int), defaultdict(int), defaultdict(int), defaultdict(int)
    gverified, gignored, gabstract, gtrusted = defaultdict(int), defaultdict(int), defaultdict(int), defaultdict(int)
    total = defaultdict(int)
    for dirname, _, files in os.walk(d):
        for f in files:
            fname = os.path.join(dirname, f)
            pkg, check = should_check(fname)
            pkg = dirname[len(d):] + ": package " + pkg
            if check and not (f.endswith("test.gobra") and not test_files):
                floc, flos, fhyb, fverified, fignored, fabstract, ftrusted, fgverified, fgignored, fgabstract, fgtrusted, ftotal = file_lines(fname)
                loc[pkg] += floc
                los[pkg] += flos
                hyb[pkg] += fhyb
                verified[pkg] += fverified
                ignored[pkg] += fignored
                abstract[pkg] += fabstract
                trusted[pkg] += ftrusted
                gverified[pkg] += fgverified
                gignored[pkg] += fgignored
                gabstract[pkg] += fgabstract
                gtrusted[pkg] += fgtrusted
                total[pkg] += ftotal
    df = pd.DataFrame([loc, los, hyb, verified, ignored, abstract, trusted, gverified, gignored, gabstract, gtrusted, total]).T
    df.columns = ['lines of code', 'lines of annotation', 'hybrid lines', 'verified functions', 'ignored functions', 'abstract functions', 'trusted functions', 'ghost verified functions', 'ghost ignored functions', 'ghost abstract functions', 'ghost trusted functions', 'total number of functions']
    df.to_csv(file_to_save)


if __name__ == "__main__":
    if len(sys.argv) < 2:
        measure_lines(".", False, "without_test.csv")
        measure_lines(".", True, "with_test.csv")
    else:
        measure_lines(sys.argv[1], False, "without_test.csv")
        measure_lines(sys.argv[1], True, "with_test.csv")
