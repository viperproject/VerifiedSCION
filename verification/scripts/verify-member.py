#!/usr/bin/env python3
"""Verify a single member of a package, instead of the whole package.

Gobra can be told to verify only the members declared on a given line of a file
(``-i <file>@<line>``); the chopper then keeps only the slice of the program that
those members need.  That is the only practical way of attributing the run time
of a package to individual functions, which is what one needs when a package
takes hours to verify.

The line numbers are a poor interface, so this script resolves a member *name*
to the line on which it is declared, and reconstructs the options that the CI
uses from ``gobra-mod.json`` and the package's ``gobra.json``.

    ./verification/scripts/verify-member.py router doXover
    ./verification/scripts/verify-member.py router rc            # a closure of Run
    ./verification/scripts/verify-member.py --list router

Note that isolation cannot currently be expressed in the JSON configuration:
``input_files`` makes Gobra fail with an internal error and ``-i`` is rejected
inside ``other``.  The script therefore assembles a full command line itself,
mirroring what the configuration files say.

The Gobra binary is taken from ``$GOBRA``; it may be either an executable or a
``.jar`` (in which case it is run with ``java -jar``).  ``$Z3_EXE`` is forwarded
to Gobra when it is set.
"""

import argparse
import json
import os
import re
import shlex
import subprocess
import sys
import time
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
MODULE_CFG = REPO / "gobra-mod.json"
JOB_CFG_NAME = "gobra.json"

# Files that Gobra reads for a package: the sources with a `// +gobra` header
# plus the specification files.  Test files are skipped, exactly as Gobra's own
# package resolver does.
SOURCE_SUFFIXES = (".go", ".gobra")


def package_files(pkg: Path):
    files = []
    for f in sorted(pkg.iterdir()):
        if f.suffix not in SOURCE_SUFFIXES or f.name.endswith("_test.go"):
            continue
        head = f.read_text(errors="replace")[:4096]
        if re.search(r"^//\s*\+gobra\s*$", head, re.M):
            files.append(f)
    return files


# A top-level declaration, e.g.
#   func (p *scionPacketProcessor) doXover( ... )
#   func newPacketProcessor( ... )
# or a named function literal, e.g.
#   func /*@ rc @*/ (ingressID uint16, ...)
DECL = re.compile(r"^\s*func\s+(?:\([^)]*\)\s*)?(\w+)\s*[({]")
CLOSURE = re.compile(r"^\s*func\s*/\*@\s*(\w+)\s*@\*/")


def members(files):
    """Map member name -> list of (file, line number)."""
    found = {}
    for f in files:
        for n, line in enumerate(f.read_text(errors="replace").split("\n"), start=1):
            m = CLOSURE.match(line) or DECL.match(line)
            if m:
                found.setdefault(m.group(1), []).append((f, n))
    return found


def merged_config(pkg: Path):
    """Merge the module-level defaults with the package's own job config.

    Mirrors Gobra's precedence: the job config wins over the module config.
    Relative paths are resolved against the directory of the file that
    declares them.
    """
    module = json.loads(MODULE_CFG.read_text()).get("default_job_cfg", {})
    job_path = pkg / JOB_CFG_NAME
    job = json.loads(job_path.read_text()) if job_path.exists() else {}

    def resolve(cfg, base):
        cfg = dict(cfg)
        if "includes" in cfg:
            cfg["includes"] = [str((base / p).resolve()) for p in cfg["includes"]]
        return cfg

    merged = resolve(module, MODULE_CFG.parent)
    merged.update(resolve(job, pkg))
    # `other` is concatenated rather than overwritten, like Gobra's merge does.
    merged["other"] = module.get("other", []) + job.get("other", [])
    return merged


# JSON field -> how it becomes a command-line option.
FLAGS = {
    "assert_timeout": lambda v: ["--assertTimeout", str(v)],
    "backend": lambda v: ["--backend", v],
    "chop": lambda v: ["--chop", str(v)],
    "mce_mode": lambda v: ["--mceMode", v],
    "module": lambda v: ["-m", v],
    "more_joins": lambda v: ["--moreJoins", v],
    "includes": lambda v: ["-I"] + list(v),
    "assume_injectivity_inhale": lambda v: ["--assumeInjectivityOnInhale" if v
                                            else "--noassumeInjectivityOnInhale"],
    "overflow": lambda v: ["--overflow" if v else "--nooverflow"],
    "check_consistency": lambda v: ["--checkConsistency"] if v else [],
    "conditionalize_permissions": lambda v: ["--conditionalizePermissions"] if v else [],
    "only_files_with_header": lambda v: ["--onlyFilesWithHeader"] if v else [],
    "parallelize_branches": lambda v: ["--parallelizeBranches"] if v else [],
    "print_vpr": lambda v: ["--printVpr"] if v else [],
    "require_triggers": lambda v: ["--requireTriggers"] if v else [],
}


def options(cfg):
    opts = []
    for key, value in cfg.items():
        if key == "other":
            opts += list(value)
        elif key in FLAGS:
            opts += FLAGS[key](value)
        # `project_root` is deliberately dropped: Gobra rejects it together with
        # `-i`, and it would withdraw the friend permissions granted to
        # `pkg/slayers`.
    return opts


def gobra_command():
    binary = os.environ.get("GOBRA")
    if not binary:
        sys.exit("Set $GOBRA to the Gobra executable or to gobra.jar.")
    if binary.endswith(".jar"):
        return ["java", "-Xss1g", "-Xmx8g", "-jar", binary]
    return [binary]


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("package", help="package directory, e.g. 'router'")
    parser.add_argument("member", nargs="?",
                        help="name of the member to verify; the whole package if omitted")
    parser.add_argument("--list", action="store_true", help="list the members and exit")
    parser.add_argument("--dry-run", action="store_true", help="print the command and exit")
    parser.add_argument("rest", nargs=argparse.REMAINDER,
                        help="further options, passed on to Gobra verbatim")
    args = parser.parse_args()

    pkg = (REPO / args.package).resolve()
    if not pkg.is_dir():
        sys.exit("no such package: %s" % pkg)
    files = package_files(pkg)
    if not files:
        sys.exit("no files with a '+gobra' header in %s" % pkg)

    declared = members(files)
    if args.list:
        for name in sorted(declared):
            for f, line in declared[name]:
                print("%-40s %s:%d" % (name, f.relative_to(REPO), line))
        return

    inputs = [str(f) for f in files]
    if args.member:
        hits = declared.get(args.member)
        if not hits:
            sys.exit("no member named %r; use --list to see the candidates"
                     % args.member)
        if len(hits) > 1:
            sys.exit("%r is declared %d times: %s" %
                     (args.member, len(hits),
                      ", ".join("%s:%d" % (f.relative_to(REPO), l) for f, l in hits)))
        target, line = hits[0]
        inputs = [str(f) + ("@%d" % line if f == target else "") for f in files]

    cmd = gobra_command() + ["-i"] + inputs + options(merged_config(pkg))
    if os.environ.get("Z3_EXE"):
        cmd += ["--z3Exe", os.environ["Z3_EXE"]]
    cmd += [a for a in args.rest if a != "--"]

    print(" ".join(shlex.quote(c) for c in cmd), flush=True)
    if args.dry_run:
        return
    start = time.time()
    rc = subprocess.call(cmd, cwd=REPO)
    print("\nfinished in %.0f s (exit code %d)" % (time.time() - start, rc))
    sys.exit(rc)


if __name__ == "__main__":
    main()
