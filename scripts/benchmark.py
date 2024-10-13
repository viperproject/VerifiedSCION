import time
import os
import pandas as pd
import argparse

SCIONPATH = None
GOBRAJAR = None

packages = {
    "verification": "java -Xss1g -Xmx4g -jar GOBRAJAR --recursive --projectRoot SCIONPATH/verification --backend SILICON --chop 1 -I SCIONPATH/verification/dependencies SCIONPATH --cacheFile .gobra/cache.json --onlyFilesWithHeader -m github.com/scionproto/scion --assumeInjectivityOnInhale --checkConsistency --mceMode=od --requireTriggers --unsafeWildcardOptimization --moreJoins off -g /tmp/",
    "pkg/addr": "java -Xss1g -Xmx4g -jar GOBRAJAR -p SCIONPATH/pkg/addr --backend SILICON --chop 1 -I SCIONPATH SCIONPATH/verification/dependencies --cacheFile .gobra/cache.json --onlyFilesWithHeader -m github.com/scionproto/scion --assumeInjectivityOnInhale --checkConsistency --mceMode=od --requireTriggers --unsafeWildcardOptimization --moreJoins off -g /tmp/",
    "pkg/experimental/epic": "java -Xss1g -Xmx4g -jar GOBRAJAR -p SCIONPATH/pkg/experimental/epic --backend SILICON --chop 1 -I SCIONPATH SCIONPATH/verification/dependencies --cacheFile .gobra/cache.json --onlyFilesWithHeader -m github.com/scionproto/scion --assumeInjectivityOnInhale --checkConsistency --mceMode=od --requireTriggers --unsafeWildcardOptimization --moreJoins off -g /tmp/",
    "pkg/log": "java -Xss1g -Xmx4g -jar GOBRAJAR -p SCIONPATH/pkg/log --backend SILICON --chop 1 -I SCIONPATH SCIONPATH/verification/dependencies --cacheFile .gobra/cache.json --onlyFilesWithHeader -m github.com/scionproto/scion --assumeInjectivityOnInhale --checkConsistency --mceMode=od --requireTriggers --unsafeWildcardOptimization --moreJoins off -g /tmp/",
    "pkg/private/serrors": "java -Xss1g -Xmx4g -jar GOBRAJAR -p SCIONPATH/pkg/private/serrors --backend SILICON --chop 1 -I SCIONPATH SCIONPATH/verification/dependencies --cacheFile .gobra/cache.json --onlyFilesWithHeader -m github.com/scionproto/scion --assumeInjectivityOnInhale --checkConsistency --mceMode=od --requireTriggers --unsafeWildcardOptimization --moreJoins off -g /tmp/",
    "pkg/scrypto": "java -Xss1g -Xmx4g -jar GOBRAJAR -p SCIONPATH/pkg/scrypto --backend SILICON --chop 1 -I SCIONPATH SCIONPATH/verification/dependencies --cacheFile .gobra/cache.json --onlyFilesWithHeader -m github.com/scionproto/scion --assumeInjectivityOnInhale --checkConsistency --mceMode=od --requireTriggers --unsafeWildcardOptimization --moreJoins off -g /tmp/",
    "pkg/slayers": "java -Xss1g -Xmx4g -jar GOBRAJAR -p SCIONPATH/pkg/slayers --backend SILICON --chop 1 -I SCIONPATH SCIONPATH/verification/dependencies --cacheFile .gobra/cache.json --onlyFilesWithHeader -m github.com/scionproto/scion --assumeInjectivityOnInhale --checkConsistency --mceMode=od --requireTriggers --unsafeWildcardOptimization --moreJoins off -g /tmp/",
    "pkg/slayers/path": "java -Xss1g -Xmx4g -jar GOBRAJAR -p SCIONPATH/pkg/slayers/path --backend SILICON --chop 1 -I SCIONPATH SCIONPATH/verification/dependencies --cacheFile .gobra/cache.json --onlyFilesWithHeader -m github.com/scionproto/scion --assumeInjectivityOnInhale --checkConsistency --mceMode=od --requireTriggers --unsafeWildcardOptimization --moreJoins off -g /tmp/",
    "pkg/slayers/path/empty": "java -Xss1g -Xmx4g -jar GOBRAJAR -p SCIONPATH/pkg/slayers/path/empty --backend SILICON --chop 1 -I SCIONPATH SCIONPATH/verification/dependencies --cacheFile .gobra/cache.json --onlyFilesWithHeader -m github.com/scionproto/scion --assumeInjectivityOnInhale --checkConsistency --mceMode=od --requireTriggers --unsafeWildcardOptimization --moreJoins off -g /tmp/",
    "pkg/slayers/path/epic": "java -Xss1g -Xmx4g -jar GOBRAJAR -p SCIONPATH/pkg/slayers/path/epic --backend SILICON --chop 1 -I SCIONPATH SCIONPATH/verification/dependencies --cacheFile .gobra/cache.json --onlyFilesWithHeader -m github.com/scionproto/scion --assumeInjectivityOnInhale --checkConsistency --mceMode=od --requireTriggers --unsafeWildcardOptimization --moreJoins off -g /tmp/",
    "pkg/slayers/path/onehop": "java -Xss1g -Xmx4g -jar GOBRAJAR -p SCIONPATH/pkg/slayers/path/onehop --backend SILICON --chop 1 -I SCIONPATH SCIONPATH/verification/dependencies --cacheFile .gobra/cache.json --onlyFilesWithHeader -m github.com/scionproto/scion --assumeInjectivityOnInhale --checkConsistency --mceMode=od --requireTriggers --unsafeWildcardOptimization --moreJoins off -g /tmp/",
    "pkg/slayers/path/scion": "java -Xss1g -Xmx4g -jar GOBRAJAR -p SCIONPATH/pkg/slayers/path/scion --backend SILICON --chop 1 -I SCIONPATH SCIONPATH/verification/dependencies --cacheFile .gobra/cache.json --onlyFilesWithHeader -m github.com/scionproto/scion --assumeInjectivityOnInhale --checkConsistency --mceMode=od --requireTriggers --unsafeWildcardOptimization --moreJoins off -g /tmp/",
    "private/topology": "java -Xss1g -Xmx4g -jar GOBRAJAR -p SCIONPATH/private/topology --backend SILICON --chop 1 -I SCIONPATH SCIONPATH/verification/dependencies --cacheFile .gobra/cache.json --onlyFilesWithHeader -m github.com/scionproto/scion --assumeInjectivityOnInhale --checkConsistency --mceMode=od --requireTriggers --unsafeWildcardOptimization --moreJoins off -g /tmp/",
    "private/topology/underlay": "java -Xss1g -Xmx4g -jar GOBRAJAR -p SCIONPATH/private/topology/underlay --backend SILICON --chop 1 -I SCIONPATH SCIONPATH/verification/dependencies --cacheFile .gobra/cache.json --onlyFilesWithHeader -m github.com/scionproto/scion --assumeInjectivityOnInhale --checkConsistency --mceMode=od --requireTriggers --unsafeWildcardOptimization --moreJoins off -g /tmp/",
    "private/underlay/conn": "java -Xss1g -Xmx4g -jar GOBRAJAR -p SCIONPATH/private/underlay/conn --backend SILICON --chop 1 -I SCIONPATH SCIONPATH/verification/dependencies --cacheFile .gobra/cache.json --onlyFilesWithHeader -m github.com/scionproto/scion --assumeInjectivityOnInhale --checkConsistency --mceMode=od --requireTriggers --unsafeWildcardOptimization --moreJoins off -g /tmp/",
    "private/underlay/sockctrl": "java -Xss1g -Xmx4g -jar GOBRAJAR -p SCIONPATH/private/underlay/sockctrl --backend SILICON --chop 1 -I SCIONPATH SCIONPATH/verification/dependencies --cacheFile .gobra/cache.json --onlyFilesWithHeader -m github.com/scionproto/scion --assumeInjectivityOnInhale --checkConsistency --mceMode=od --requireTriggers --unsafeWildcardOptimization --moreJoins off -g /tmp/",
    "router/bfd": "java -Xss1g -Xmx4g -jar GOBRAJAR -p SCIONPATH/router/bfd --backend SILICON --chop 1 -I SCIONPATH SCIONPATH/verification/dependencies --cacheFile .gobra/cache.json --onlyFilesWithHeader -m github.com/scionproto/scion --assumeInjectivityOnInhale --checkConsistency --mceMode=od --requireTriggers --unsafeWildcardOptimization --moreJoins off -g /tmp/",
    "router/control": "java -Xss1g -Xmx4g -jar GOBRAJAR -p SCIONPATH/router/control --backend SILICON --chop 1 -I SCIONPATH SCIONPATH/verification/dependencies --cacheFile .gobra/cache.json --onlyFilesWithHeader -m github.com/scionproto/scion --assumeInjectivityOnInhale --checkConsistency --mceMode=od --requireTriggers --unsafeWildcardOptimization --moreJoins off -g /tmp/",
    "router": "java -Xss1g -Xmx4g -jar GOBRAJAR -p SCIONPATH/router --backend SILICON --chop 1 -I SCIONPATH SCIONPATH/verification/dependencies --cacheFile .gobra/cache.json --onlyFilesWithHeader -m github.com/scionproto/scion --assumeInjectivityOnInhale --checkConsistency --mceMode=on --parallelizeBranches --requireTriggers --conditionalizePermissions --moreJoins impure -g /tmp/",
}

timeouts = {
    "verification": 180,
    "pkg/addr": 50,
    "pkg/experimental/epic": 300,
    "pkg/log": 20,
    "pkg/private/serrors": 25,
    "pkg/scrypto": 20,
    "pkg/slayers": 360,
    "pkg/slayers/path": 180,
    "pkg/slayers/path/empty": 120,
    "pkg/slayers/path/epic": 120,
    "pkg/slayers/path/onehop": 120,
    "pkg/slayers/path/scion": 1440,
    "private/topology": 50,
    "private/topology/underlay": 50,
    "private/underlay/conn": 60,
    "private/underlay/sockctrl": 30,
    "router/bfd": 30,
    "router/control": 50,
    "router": 7200,
}


def timeit(c, timeout):
    s = time.time()
    os.popen(f"timeout {timeout} {c}").read()
    return time.time() - s

TRIES = 5

def benchmark():
    times = {}
    for p, c in packages.items():
        times[p] = []
        for t in range(TRIES):
            times[p].append(timeit(c, timeouts[p]))
    data = []
    # gather the data in a pandas dataframe
    for p in packages.keys():
        data.append([p, *times[p]])
    df = pd.DataFrame(data, columns=["package", *range(TRIES)])
    df.to_csv("benchmark.csv", index=False)


if __name__ == "__main__":
    # gather the command line arguments SCIONPATH and GOBRAJAR
    # the arguments are required
    parser = argparse.ArgumentParser()
    parser.add_argument("scionpath", help="Path to the SCION repository")
    parser.add_argument("gobrajar", help="Path to the gobra jar file")
    args = parser.parse_args()
    SCIONPATH = args.scionpath
    # fix scionpath to not end with a slash
    if SCIONPATH[-1] == "/":
        SCIONPATH = SCIONPATH[:-1]
    GOBRAJAR = args.gobrajar
    # replace the placeholders in the commands
    for p in packages.keys():
        packages[p] = packages[p].replace("SCIONPATH", SCIONPATH).replace("GOBRAJAR", GOBRAJAR)
    benchmark()
