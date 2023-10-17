import os
import re

def read_env_var_or_crash(name):
    val = os.getenv(name)
    if val is None:
        print(f'Environment variable {name} not found.')
        print('If the environment var contains a path, please ensure it is an absolut path.')
        exit(1)
    else:
        return val

def run_cmd_or_exit(cmd, err_msg):
    exit_code = os.system(cmd)
    if exit_code != 0:
        exit(err_msg)

def isvalidgitbranch(str):
    return re.fullmatch(r"([a-zA-Z0-9_])+", str) is not None