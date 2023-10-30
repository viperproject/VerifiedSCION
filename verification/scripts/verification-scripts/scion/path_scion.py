from . import defs

path_files_rel_paths = [
    "pkg/slayers/path/scion/base.go",
    "pkg/slayers/path/scion/base_spec.gobra",
    "pkg/slayers/path/scion/decoded.go",
    "pkg/slayers/path/scion/decoded_spec.gobra",
    "pkg/slayers/path/scion/raw.go",
    "pkg/slayers/path/scion/raw_spec.gobra",
]

path_test_files_rel_paths = [
    "pkg/slayers/path/scion/base_spec_test.gobra",
    "pkg/slayers/path/scion/decoded_spec_test.gobra",
    "pkg/slayers/path/scion/raw_spec_test.gobra",
]

path_files = list(map(defs.relative_path, path_files_rel_paths))
path_test_files = list(map(defs.relative_path, path_test_files_rel_paths))

path_cfg = defs.GobraConfig(
    inputs = path_files,
    # testFiles = dataplane_test_files_rel_paths,
    conditionalizePermissions = False,
    mceMode = "on",
    parallelizeBranches = True,
)
