from . import defs

dataplane_files_rel_paths = [
    "router/dataplane.go",
    "router/bfd_spec.gobra",
    "router/dataplane_spec.gobra",
    "router/metrics_spec.gobra",
    "router/metrics.go",
    "router/svc_spec.gobra",
    "router/svc.go",
]

dataplane_test_files_rel_paths = [
    "router/dataplane_spec_test.gobra",
    "router/svc_spec_test.gobra",
]

dataplane_files = list(map(defs.relative_path, dataplane_files_rel_paths))
dataplane_test_files = list(map(defs.relative_path, dataplane_test_files_rel_paths))

dataplane_cfg = defs.GobraConfig(
    inputs = dataplane_files,
    # testFiles = dataplane_test_files_rel_paths,
    conditionalizePermissions = True,
    mceMode = "on",
    parallelizeBranches = True,
)
