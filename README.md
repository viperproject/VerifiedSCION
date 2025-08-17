# Protocols to Code: Formal Verification of a Secure Next-Generation Internet Router

## README file accompanying sources of paper submission

description: Annotated codebase of SCION

This folder contains an annotated version of the SCION repository. Below, we list the main packages, containing most of the annotations, and we give details on how to reproduce the verification of these packages.

In this README, we (1) explain how to install and use Gobra, (2) explain how the verified codebase of SCION is organized, and (3) explain how to verify these files in the command line.
Assuming the acceptance of the paper, we will provide a fully set-up environment ready to verify the entire project for the artifact evaluation.

Installing Gobra
--------------------------------------------------------------------------------
  The provided code-base can be verified using Gobra. We provide a pre-built file `/artifact/bin/gobra.jar` that can be used already. You can also build Gobra from source. Instructions on how to obtain and install Gobra are available on the project's Github page: [https://github.com/viperproject/gobra](https://github.com/viperproject/gobra).

  Besides the `gobra.jar` file, you need the following dependencies to run Gobra:
  1. A valid installation of Java 64-bit Version 11
  2. A valid installation of the Z3 theorem prover, version `4.8.7`. Instructions on how to install it can be found [here](https://github.com/Z3Prover/z3), and you can also download pre-built binaries for your platform [here](https://github.com/Z3Prover/z3/releases).

**Note 1: The provided docker image comes pre-installed with the correct versions of the dependencies. If you are reproducing these instructions elsewhere,
make sure that you have the correct versions of the dependencies, otherwise you may run into issues when running the commands below.**

**Note 2: If you opt to build Gobra yourself, please fetch the commit `9a386be` of Gobra.**

Structure of the codebase
--------------------------------------------------------------------------------
The verified codebase of SCION is a fork of the official SCION GitHub repository.
While we often incorporated changes from upstream in our code base, we fixed the SCION version
to the upstream commit c6f12ba prior to the submission of this paper to have a stable target.

The verified codebase of SCION has the same file structure as the original project. Of note, this repository includes all major components of SCION, but in this project we only focused on the router, whose implementation is spread across the following Go packages:
1. `pkg/addr` - provides definitions of structures representing host addresses and Isolation Domain identifiers
2. `pkg/experimental/epic` - functionality to process packets with the EPIC extension
3. `pkg/slayers` - contains the definition of structures representing SCION packets. After the `router` package, this is the most important package of the verified codebase
4. `pkg/slayers/path` - defines a generic Go interface named `Path` which describes abstracts over all possible kinds of paths stored in a packet
5. `pkg/slayers/path/empty` - defines an implementation of `Path` representing an empty path
6. `pkg/slayers/path/epic` - defines an implementation of `Path` for EPIC paths
7. `pkg/slayers/path/onehop` - defines an implementation of `Path` for paths consisting of a single hop (e.g., for use during the configuration of the router)
8. `pkg/slayers/path/scion` - defines an implementation of `Path` for regular SCION packets consisting of one to three infofields, where each infofield may have multiple hops
9. `private/topology` - implements functionality related to network topology. The only relevant Go file in this package is `linktype.go`, which defines the kinds of links allowed by Autonomous Systems (i.e., `Parent`, `Child`, `Core`, and `Peer`)
10. `private/topology/underlay` - minor dependency, contains definitions of constants representing combinations of network protocols (e.g., `UDPIPv4Name  = "UDP/IPv4"`)
11. `private/underlay/conn` - defines UDP connections.
12. `router` - this is **the main package**. It contains the implementation of the border router in the file `dataplane.go`. In that file, we have the definition of the data structure `DataPlane` which describes the internal and external connections of the router. Apart from that, it contains the definition of the method `Run` which starts the router after its configuration. This function starts a thread per connection of the router that listens to batches of new packages, processes them (by calling the `processPkt` function), and then forwards each packet in the network. `Run` is the entry point of the router, and all relevant functions are directly or indirectly called from that function.

In the list above, we follow the convention of identifying each package by the relative path to the root of the project, instead of listing it by name only.
Each package in Go is composed of multiple `.go` files containing Go code. For all of the packages listed above, we provide specifications (and verify them!) for all `.go` files whose functionality is relevant to the forwarding logic of the router. This excludes files that provide functionality for external clients of the SCION packages like pretty printing (e.g., file `fmt.go` in package `pkg/addr`). We identify the files that are relevant for verification with the annotation `// +gobra` after the license header. Note that the files that were ignored do not count toward the 4.700 LoC reported in the paper. In the packages listed above, there are also files with the extension `.gobra`. These files contain lemmas and definitions of data structures, functions, and predicates that are useful for proving the correctness of the router.

Finally, the folder `verification` contains three subfolders:
- `dependencies` - contains our formalization of parts of the Go standard library, parts of the `prometheus` library for Go, and parts of the library `gopacket`
- `io` - contains the complete specification of the I/O behaviour of the router and auxiliary definitions
- `utils` - contains lemmas and definitions that are generally useful for proofs

Note: For navigating the codebase, we recommend using the Gobra IDE extension for VSCode to enable syntax highlighting in `.gobra` files. More details about the extension, as well as instructions on how to install it, are available at https://marketplace.visualstudio.com/items?itemName=viper-admin.gobra-ide.


Verifying the code base
--------------------------------------------------------------------------------
To verify each of the packages that we listed, you need a file `gobra.jar` ready to be executed. You may use the one we provided, or the one that you built yourself.
You also need the correct version of the dependencies (Java and Z3) installed.

As a final step before running the commands, you need to define an environment variable named `Z3_EXE` that contains the absolute path for your z3 executable. In Unix-based operating systems, you can do this using the following command, where `PATH_TO_Z3` is a placeholder for your z3 binary:
```sh
export Z3_EXE=PATH_TO_Z3
```
**NOTE: If z3 is installed and available on your PATH, you can find out its absolute path with the command `which z3`.**

To verify each package, use the respective command listed below.

1. `pkg/addr`
```sh
java -Xss1g -Xmx4g -jar /artifact/bin/gobra.jar -p ./pkg/addr -I . ./verification/dependencies --onlyFilesWithHeader -m github.com/scionproto/scion --mceMode=od
```
2. `pkg/experimental/epic`
```sh
java -Xss1g -Xmx4g -jar /artifact/bin/gobra.jar -p ./pkg/experimental/epic -I . ./verification/dependencies --onlyFilesWithHeader -m github.com/scionproto/scion --mceMode=od
```
3. `pkg/slayers`
```sh
java -Xss1g -Xmx4g -jar /artifact/bin/gobra.jar -p ./pkg/slayers -I . ./verification/dependencies --onlyFilesWithHeader -m github.com/scionproto/scion --mceMode=od
```
4. `pkg/slayers/path`
```sh
java -Xss1g -Xmx4g -jar /artifact/bin/gobra.jar -p ./pkg/slayers/path -I . ./verification/dependencies --onlyFilesWithHeader -m github.com/scionproto/scion --mceMode=od
```
5. `pkg/slayers/path/empty`
```sh
java -Xss1g -Xmx4g -jar /artifact/bin/gobra.jar -p ./pkg/slayers/path/empty -I . ./verification/dependencies --onlyFilesWithHeader -m github.com/scionproto/scion --mceMode=od
```
6. `pkg/slayers/path/epic`
```sh
java -Xss1g -Xmx4g -jar /artifact/bin/gobra.jar -p ./pkg/slayers/path/epic -I . ./verification/dependencies --onlyFilesWithHeader -m github.com/scionproto/scion --mceMode=od
```
7. `pkg/slayers/path/onehop`
```sh
java -Xss1g -Xmx4g -jar /artifact/bin/gobra.jar -p ./pkg/slayers/path/onehop -I . ./verification/dependencies --onlyFilesWithHeader -m github.com/scionproto/scion --mceMode=od
```
8. `pkg/slayers/path/scion`
```sh
java -Xss1g -Xmx4g -jar /artifact/bin/gobra.jar -p ./pkg/slayers/path/scion -I . ./verification/dependencies --onlyFilesWithHeader -m github.com/scionproto/scion --mceMode=od
```
9. `private/topology`
```sh
java -Xss1g -Xmx4g -jar /artifact/bin/gobra.jar -p ./private/topology -I . ./verification/dependencies --onlyFilesWithHeader -m github.com/scionproto/scion --mceMode=od
```
10. `private/topology/underlay`
```sh
java -Xss1g -Xmx4g -jar /artifact/bin/gobra.jar -p ./private/topology/underlay -I . ./verification/dependencies --onlyFilesWithHeader -m github.com/scionproto/scion --mceMode=od
```
11. `private/underlay/conn`
```sh
java -Xss1g -Xmx4g -jar /artifact/bin/gobra.jar -p ./private/underlay/conn -I . ./verification/dependencies --onlyFilesWithHeader -m github.com/scionproto/scion --mceMode=od
```
12. `router`
```sh
java -Xss1g -Xmx4g -jar /artifact/bin/gobra.jar -p ./router -I . ./verification/dependencies --onlyFilesWithHeader -m github.com/scionproto/scion --mceMode=on --parallelizeBranches --moreJoins impure
```

Note that verifying the first 11 packages combined should take up to 15 minutes. Verifying the package `router` may take much longer. On our machine (a Macbook Pro 16' 2023 with an Apple M2 Max), it takes up to 45 minutes.

Note: on lower-end or older machines, you may experience spurious errors when verifying the dataplane. If that happens, please re-execute the command.

The output of Gobra has the following shape:
```
(c) Copyright ETH Zurich 2012 - 2022
22:42:49.847 [main] INFO viper.gobra.Gobra - Verifying package ./pkg/addr - addr [22:42:49]
22:43:02.556 [main] INFO viper.gobra.Gobra - Gobra found 0 errors
```
Note that the line that matters here is `22:43:02.556 [main] INFO viper.gobra.Gobra - Gobra found 0 errors`, which confirms a successful verification.

