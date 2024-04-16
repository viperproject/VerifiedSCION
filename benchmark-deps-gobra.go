// Copyright 2024 ETH Zurich
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//   http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// This file is meant to be used as a script to benchmarks the verification
// of the dependencies of the router. By default, this runs each relevant
// package three times and reports the results as a .csv.

package main

import (
	"fmt"
	"log"
	"os/exec"
	"strings"
	"time"
)

const runs = 3
const gobraCmd = "/usr/bin/java -Xss1g -Xmx4g -jar"
const gobraFlags = "/Users/joao/tools/gobra/master_20240414185033/gobra.jar"

var commands = map[string]string{
	"verification":              "--recursive --projectRoot ./verification --backend SILICON --chop 1 -I ./verification/dependencies . --cacheFile .gobra/cache.json --onlyFilesWithHeader -m github.com/scionproto/scion --assumeInjectivityOnInhale --checkConsistency --mceMode=od --requireTriggers --unsafeWildcardOptimization",
	"pkg/addr":                  "-p ./pkg/addr --backend SILICON --chop 1 -I . ./verification/dependencies --cacheFile .gobra/cache.json --onlyFilesWithHeader -m github.com/scionproto/scion --assumeInjectivityOnInhale --checkConsistency --mceMode=od --requireTriggers --unsafeWildcardOptimization",
	"pkg/experimental/epic":     "-p ./pkg/experimental/epic --backend SILICON --chop 1 -I . ./verification/dependencies --cacheFile .gobra/cache.json --onlyFilesWithHeader -m github.com/scionproto/scion --assumeInjectivityOnInhale --checkConsistency --mceMode=od --requireTriggers --unsafeWildcardOptimization",
	"pkg/log":                   "-p ./pkg/log --backend SILICON --chop 1 -I . ./verification/dependencies --cacheFile .gobra/cache.json --onlyFilesWithHeader -m github.com/scionproto/scion --assumeInjectivityOnInhale --checkConsistency --mceMode=od --requireTriggers --unsafeWildcardOptimization",
	"pkg/private/serrors":       "-p ./pkg/private/serrors --backend SILICON --chop 1 -I . ./verification/dependencies --cacheFile .gobra/cache.json --onlyFilesWithHeader -m github.com/scionproto/scion --assumeInjectivityOnInhale --checkConsistency --mceMode=od --requireTriggers --unsafeWildcardOptimization",
	"pkg/scrypto":               "-p ./pkg/scrypto --backend SILICON --chop 1 -I . ./verification/dependencies --cacheFile .gobra/cache.json --onlyFilesWithHeader -m github.com/scionproto/scion --assumeInjectivityOnInhale --checkConsistency --mceMode=od --requireTriggers --unsafeWildcardOptimization",
	"pkg/slayers":               "-p ./pkg/slayers --backend SILICON --chop 1 -I . ./verification/dependencies --cacheFile .gobra/cache.json --onlyFilesWithHeader -m github.com/scionproto/scion --assumeInjectivityOnInhale --checkConsistency --mceMode=od --requireTriggers --unsafeWildcardOptimization",
	"pkg/slayers/path":          "-p ./pkg/slayers/path --backend SILICON --chop 1 -I . ./verification/dependencies --cacheFile .gobra/cache.json --onlyFilesWithHeader -m github.com/scionproto/scion --assumeInjectivityOnInhale --checkConsistency --mceMode=od --requireTriggers --unsafeWildcardOptimization",
	"pkg/slayers/path/empty":    "-p ./pkg/slayers/path/empty --backend SILICON --chop 1 -I . ./verification/dependencies --cacheFile .gobra/cache.json --onlyFilesWithHeader -m github.com/scionproto/scion --assumeInjectivityOnInhale --checkConsistency --mceMode=od --requireTriggers --unsafeWildcardOptimization",
	"pkg/slayers/path/epic":     "-p ./pkg/slayers/path/epic --backend SILICON --chop 1 -I . ./verification/dependencies --cacheFile .gobra/cache.json --onlyFilesWithHeader -m github.com/scionproto/scion --assumeInjectivityOnInhale --checkConsistency --mceMode=od --requireTriggers --unsafeWildcardOptimization",
	"pkg/slayers/path/onehop":   "-p ./pkg/slayers/path/onehop --backend SILICON --chop 1 -I . ./verification/dependencies --cacheFile .gobra/cache.json --onlyFilesWithHeader -m github.com/scionproto/scion --assumeInjectivityOnInhale --checkConsistency --mceMode=od --requireTriggers --unsafeWildcardOptimization",
	"pkg/slayers/path/scion":    "-p ./pkg/slayers/path/scion --backend SILICON --chop 1 -I . ./verification/dependencies --cacheFile .gobra/cache.json --onlyFilesWithHeader -m github.com/scionproto/scion --assumeInjectivityOnInhale --checkConsistency --mceMode=od --requireTriggers --unsafeWildcardOptimization",
	"private/topology":          "-p ./private/topology --backend SILICON --chop 1 -I . ./verification/dependencies --cacheFile .gobra/cache.json --onlyFilesWithHeader -m github.com/scionproto/scion --assumeInjectivityOnInhale --checkConsistency --mceMode=od --requireTriggers --unsafeWildcardOptimization",
	"private/topology/underlay": "-p ./private/topology/underlay --backend SILICON --chop 1 -I . ./verification/dependencies --cacheFile .gobra/cache.json --onlyFilesWithHeader -m github.com/scionproto/scion --assumeInjectivityOnInhale --checkConsistency --mceMode=od --requireTriggers --unsafeWildcardOptimization",
	"private/underlay/conn":     "-p ./private/underlay/conn --backend SILICON --chop 1 -I . ./verification/dependencies --cacheFile .gobra/cache.json --onlyFilesWithHeader -m github.com/scionproto/scion --assumeInjectivityOnInhale --checkConsistency --mceMode=od --requireTriggers --unsafeWildcardOptimization",
	"private/underlay/sockctrl": " -p ./private/underlay/sockctrl --backend SILICON --chop 1 -I . ./verification/dependencies --cacheFile .gobra/cache.json --onlyFilesWithHeader -m github.com/scionproto/scion --assumeInjectivityOnInhale --checkConsistency --mceMode=od --requireTriggers --unsafeWildcardOptimization",
	"router/bfd":                "-p ./router/bfd --backend SILICON --chop 1 -I . ./verification/dependencies --cacheFile .gobra/cache.json --onlyFilesWithHeader -m github.com/scionproto/scion --assumeInjectivityOnInhale --checkConsistency --mceMode=od --requireTriggers --unsafeWildcardOptimization",
	"router/control":            "-p ./router/control --backend SILICON --chop 1 -I . ./verification/dependencies --cacheFile .gobra/cache.json --onlyFilesWithHeader -m github.com/scionproto/scion --assumeInjectivityOnInhale --checkConsistency --mceMode=od --requireTriggers --unsafeWildcardOptimization",
}

var verificationTimes = map[string]([]float64){}

func main() {
	for pkg, cmdSuffix := range commands {
		fmt.Println("Benchmarking ", pkg)
		for i := 0; i < runs; i += 1 {
			fmt.Println("Run: ", i+1)
			start := time.Now()
			cmdStr := strings.Join([]string{gobraCmd, gobraFlags, cmdSuffix}, " ")
			cmd := exec.Command("zsh", "-c", cmdStr)
			if output, err := cmd.CombinedOutput(); err != nil {
				outputStr := string(output)
				log.Fatal(outputStr)
				return
			}
			elapsed := time.Since(start)
			verificationTimes[pkg] = append(verificationTimes[pkg], elapsed.Seconds())
		}
	}
	fmt.Println("Verification times as csv:")
	fmt.Println("--------------------------")
	fmt.Println("Package, Run 1 (s), Run 2 (s), Run 3 (s)")
	for pkg, times := range verificationTimes {
		fmt.Println(pkg, ",", times[0], ",", times[1], ",", times[2])
	}
}
