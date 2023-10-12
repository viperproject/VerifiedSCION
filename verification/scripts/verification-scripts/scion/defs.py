import os
import platform
import utils
from pathlib import Path

# TODO:
# - a very lax thread model is assumed. In the future, perform proper sanitization of inputs

# env
VERIFIEDSCION_DIR_VAR_NAME = 'VERIFIEDSCION_PATH'
VERIFIEDSCION_DIR = utils.read_env_var_or_crash(VERIFIEDSCION_DIR_VAR_NAME)
VERIFIEDSCION_PATH = Path(VERIFIEDSCION_DIR)

def relative_path(rel_path):
    path: Path = Path(VERIFIEDSCION_PATH) / rel_path
    return str(path)

default_includes = [
    VERIFIEDSCION_PATH,
    VERIFIEDSCION_PATH / "verification" / "dependencies",
]

default_module = "github.com/scionproto/scion"

class GobraConfig:
    def __init__(self,
                 assumeInjectivityOnInhale = True,
                 backend = "SILICON",
                 checkConsistency = True,
                 chop = None,
                 conditionalizePermissions = False,
                 directory = list(),
                 includePackages = default_includes,
                 # the name of the option below in Gobra is 'input', but this
                 # is a keyword in python.
                 inputs = list(),
                 testFiles = list(),
                 mceMode = "on",
                 module = default_module,
                 onlyFilesWithHeader = True,
                 parallelizeBranches = False,
                 printVpr = True,
                 projectRoot = None,
                 recursive = False,
                 requireTriggers = True):
        self.assumeInjectivityOnInhale = assumeInjectivityOnInhale
        self.backend = backend
        self.checkConsistency = checkConsistency
        self.chop = chop
        self.conditionalizePermissions = conditionalizePermissions
        self.directory = directory
        self.includePackages = includePackages
        self.inputs = inputs
        self.testFiles = testFiles
        self.mceMode = mceMode
        self.module = module
        self.onlyFilesWithHeader = onlyFilesWithHeader
        self.parallelizeBranches = parallelizeBranches
        self.printVpr = printVpr
        self.projectRoot = projectRoot
        self.recursive = recursive
        self.requireTriggers = requireTriggers

    def to_flag_str(self) -> str:
        flag_str: str = 'gobra'
        if self.assumeInjectivityOnInhale:
            flag_str = flag_str + ' --assumeInjectivityOnInhale'
        flag_str = flag_str + f' --backend={self.backend}'
        if self.checkConsistency:
            flag_str = flag_str + ' --checkConsistency'
        if self.chop is not None:
            flag_str = flag_str + f' chop={self.chop}'
        if self.conditionalizePermissions:
            flag_str = flag_str + ' --conditionalizePermissions'
        if self.directory:
            dir_str = ' '.join(self.directory)
            flag_str = flag_str + f' --directory {dir_str}'
        if self.includePackages:
            # TODO: this takes a list of Paths, the other options take a list of
            # strs. Make it uniform
            include_paths = map(os.path.abspath, self.includePackages)
            include_path = ' '.join(include_paths)
            flag_str = flag_str + f' -I {include_path}'
        if self.inputs or self.testFiles:
            all_inputs = self.inputs + self.testFiles
            inputs = ' '.join(all_inputs)
            flag_str = flag_str + f' -i {inputs}'
        flag_str = flag_str + f' --mceMode {self.mceMode}'
        flag_str = flag_str + f' -m {self.module}'
        if self.onlyFilesWithHeader:
            flag_str = flag_str + ' --onlyFilesWithHeader'
        if self.parallelizeBranches:
            flag_str = flag_str + ' --parallelizeBranches'
        if self.printVpr:
            flag_str = flag_str + ' --printVpr'
        if self.projectRoot is not None:
            exit("Project root option not yet implemented")
        if self.recursive:
            flag_str = flag_str + ' --recursive'
        if self.requireTriggers:
            flag_str = flag_str + ' --requireTriggers'
        return flag_str
    
    def notification_str(self):
        flag_str = ''
        if self.directory:
            dir_str = ' '.join(self.directory)
            flag_str = flag_str + f' --directory {dir_str}'
        if self.inputs or self.testFiles:
            all_inputs = self.inputs + self.testFiles
            inputs = ' '.join(all_inputs)
            flag_str = flag_str + f' -i {inputs}'
        flag_str = flag_str + f' --mceMode {self.mceMode}'
        if self.parallelizeBranches:
            flag_str = flag_str + ' --parallelizeBranches'
        if self.printVpr:
            flag_str = flag_str + ' --printVpr'
        if self.recursive:
            flag_str = flag_str + ' --recursive'
        return flag_str



def record_run():
    # TODO: save the config that was executed (flags),
    # save a zip of scion package (without .git),
    # save the commits or the name of the Gobra, silicon, and viperserver
    # deps, verification time,
    pass

def call_gobra(config: GobraConfig, color=True, sound=False, notification=False):
    cmd_str = config.to_flag_str()
    print(f'Running {cmd_str}')
    color_cmd_suffix = "| grep --color=always 'Error at: <.*>.*\|$'"
    if color:
        cmd_str = f'{cmd_str} {color_cmd_suffix}'
    # not working
    # result_success = os.system(cmd_str) == 0
    os.system(cmd_str)
    if sound:
        print('\a\a\a\a')
    if notification and platform.system() == 'Darwin':
        # not working
        # result_msg = "SUCCESS" if result_success else "FAILURE"
        mac_notification = f"osascript -e 'display notification \"{config.notification_str()}\" with title \"Verification Finished\"'"
        os.system(mac_notification)
