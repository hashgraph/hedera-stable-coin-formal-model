Hedera Stablecoin - Formal Model
=================================================


## Introduction

The [K Framework](https://github.com/kframework/) makes it possible to rigorously verify specifications. We make many assumptions like those of the EVM and provide a specification of a stablecoin.

## Structure

Specifications are formalized in files ending in `-spec.k`.

## Usage

To run, we recommend the docker version of the K-framework. Then to run the
commands in the `k` framework, you can do the following.

1. Checkout this repo somewhere.
1. Run `docker run -it -v /your-path-to-this-repo/hedera-stablecoin:/root/hcs runtimeverificationinc/kframework-k:ubuntu-bionic-bbc70cb`
1. `cd root/hcs`
1. `make` (to build and prove all the specifications)

Alternatively, you can build the main module:
`kompile --backend java hcs.k`

and prove a single specification:
`kprove compliant-spec.k` (or any other file ending in `-spec.k`)

Proving a specification shold output `#True` (and maybe some warnings).

## Acknowledgments

Based on the [ERC-20 Formal Model](https://github.com/runtimeverification/erc20-semantics) of [Grigore Rosu](http://fsl.cs.illinois.edu/grosu).
