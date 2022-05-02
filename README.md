# VerifiedSCION

This package contains the **verified** implementation of the
[SCION](http://www.scion-architecture.net) protocol, a future Internet architecture.
SCION is the first
clean-slate Internet architecture designed to provide route control, failure
isolation, and explicit trust information for end-to-end communication.

![VerifiedSCION sticker](./logo.png)

To find out more about the project, please visit the [official project page](https://www.pm.inf.ethz.ch/research/verifiedscion.html).

> We are currently in the process of migrating the specifications and other annotations from the [original VerifiedSCION repository](https://github.com/jcp19/VerifiedSCION) to this one. This repository contains an up-to-date version of SCION (which we plan to keep updated), as well as improvements resulting from our experience from our first efforts on verifying SCION.

## Methodology
We focus on verifying the main implementation of SCION, written in the *Go* programming language.

To that end, we have developed [Gobra](https://www.pm.inf.ethz.ch/research/gobra.html), a program verifier for Go. Gobra allows users to annotate Go code with specifications in the form of logical assertions establishing the behaviour of the program. 
It then automatically checks whether the implementation matches its given specification.
We use Gobra in the CI of this project via the [gobra-action](https://github.com/viperproject/gobra-action) to verify our code-base.

In this project, we aim at verifying the data-plane component of the SCION border router. In particular, we verify the following properties:
1. memory safety, crash freedom, and race-freedom of the SCION data-plane code
2. progress properties and termination of the data-plane code
3. the IO behaviour of the router successfully refines the SCION protocol - we prove this property only the handling of packets of type `SCION` (i.e., we ignore `BFD` packages for now)

When necessary, we make reasonable assumptions and explicitly state them.

## Differences to `scionproto/scion`
This repository is meant to be updated frequently, to keep track of the changes in the SCION implementation ([scionproto/scion](https://github.com/scionproto/scion/)). The current version of this repository is based on the commit [cc378aaf5ac028995b3697d6ed9ad98d9a166227SCION](https://github.com/scionproto/scion/tree/cc378aaf5ac028995b3697d6ed9ad98d9a166227) from the original repository.

Whenever necessary, we transform the original code to make it easier to verify (e.g., by extracting closures to a named function). We try to have minimal differences from the original code and we expect to contribute these changes to the upstream when we believe that they improve the original code.

## Repo Structure
This repository contains all the code from `scionproto/scion`.
Its directory structure is the same as the SCION repository, except that it includes the `verification` directory, which contains useful definitions for specifying and verifying the border router:
```
verification
├── dependencies # spec of 3rd-party dependencies
└── utils
    ├── definitions # useful definitions
    └── slices # slice predicates and operations
```

To specify and verify the border router, we often add specifications in `.go` files directly. We also introduce `.gobra` files containing ghost-code and predicate definitions specific to a package.

## License
[![License](https://img.shields.io/github/license/scionproto/scion.svg?maxAge=2592000)](https://github.com/scionproto/scion/blob/master/LICENSE)