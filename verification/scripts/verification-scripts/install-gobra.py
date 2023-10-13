## Script to install and manage versions of Gobra

import argparse
from pathlib import Path
import os
import shutil
import time
import utils

INSTAL_DIR = utils.read_env_var_or_crash('GOBRA_INSTALLS')
GOBRA_REPO = utils.read_env_var_or_crash('GOBRA_REPO')
GOBRA_CMD_FILE = utils.read_env_var_or_crash('GOBRA_CMD_FILE')
USER_TMP_DIR = utils.read_env_var_or_crash('USER_TMP_FOLDER')
DEFAULT_FILE = '.default'
GOBRA_VERSION_FILE = Path(INSTAL_DIR) / DEFAULT_FILE
USER_TMP_DIR_PATH = Path(USER_TMP_DIR) 

# TODO:
# - init command that setups up all directories, touches the cmd file and makes it executable (chmod)
# - the thread model is a bit loose yet. This script may allow for shell injection
# - allow the user to specify the branch of silicon and fetch it

def cli_parser():
    # create the top-level parser
    parser = argparse.ArgumentParser(prog='gobra-install')
    parser.set_defaults(func=lambda _: parser.print_help())
    subparsers = parser.add_subparsers()

    parser_install = subparsers.add_parser('install', help='install a Gobra version')
    parser_install.add_argument('branch')
    parser_install.add_argument('--set', action=argparse.BooleanOptionalAction)
    parser_install.set_defaults(func=install)

    parser_list = subparsers.add_parser('list', help='list all installed versions of Gobra')
    parser_list.set_defaults(func=list_gobra)

    parser_set = subparsers.add_parser('set', help='set version of Gobra to run by default')
    parser_set.add_argument('version')
    parser_set.set_defaults(func=set_gobra)
    return parser

def install(args):
    assert utils.isvalidgitbranch(args.branch), "The provided branch name is not a valid identifier"
    clone = f'git clone --recurse-submodules {GOBRA_REPO}'
    change_branch = f'git checkout {args.branch} > /dev/null 2>&1'
    assembly = 'sbt assembly'

    target_dir = USER_TMP_DIR_PATH / 'gobra'
    date = time.strftime('%Y%m%d%H%M%S')
    output_dir = f'{args.branch}_{date}'
    output_dir_path = Path(INSTAL_DIR) / output_dir

    if not os.path.exists(target_dir):
        os.chdir(USER_TMP_DIR_PATH)
        exit_code = os.system(clone)
        if exit_code != 0:
            exit("Failed to clone repo")
    os.chdir(target_dir)
    exit_code = os.system(change_branch)
    if exit_code != 0:
        exit(f'Branch {args.branch} not found')
    exit_code = os.system('git pull')
    if exit_code != 0:
        exit("Failed to pull the most recent version of the branch")
    exit_code = os.system(assembly)
    if exit_code != 0:
        exit("Failed to build Gobra")
    os.mkdir(output_dir_path)
    shutil.move(USER_TMP_DIR_PATH / 'gobra' / 'target' / 'scala-2.13' / 'gobra.jar', output_dir_path)
    if args.set:
        set_gobra_helper(output_dir)

def list_gobra(args):
    files = os.listdir(INSTAL_DIR)
    default = None
    if GOBRA_VERSION_FILE.name in files:
        with open(GOBRA_VERSION_FILE, 'r') as gobra_version_file:
            default = gobra_version_file.read().strip()
    print("Installed versions:")
    for f in files:
        if f == GOBRA_VERSION_FILE.name:
            pass
        elif f == default:
            print(f'* {f}')
        else:
            print(f'- {f}')

def set_gobra(args):
    assert utils.isvalidgitbranch(args.version), "The provided version name is not a valid identifier"
    if not os.path.exists(Path(INSTAL_DIR) / args.version):
        exit("The version could not be found")
    set_gobra_helper(args.version)

def set_gobra_helper(version):
    Path(GOBRA_VERSION_FILE).touch(exist_ok=True)
    Path(GOBRA_CMD_FILE).touch(exist_ok=True)
    with open(GOBRA_VERSION_FILE, 'w') as gobra_version_file:
        gobra_version_file.write(version)
    with open(GOBRA_CMD_FILE, 'w') as gobra_cmd_file:
        shebang = '#!/usr/bin/env bash\n'
        path_exec = Path(INSTAL_DIR) / version / 'gobra.jar'
        cmd = f'java -Xss128m -Xmx4g -jar {path_exec} "$@"'
        # generate executable file
        gobra_cmd_file.write(shebang)
        gobra_cmd_file.write(cmd)

if __name__ == "__main__":
    parser = cli_parser()
    args = parser.parse_args()
    args.func(args)

