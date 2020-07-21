Hedera Stablecoin - Formal Model
=================================================


## Introduction

The [K Framework](https://github.com/kframework/) makes it possible to
rigorously verify specifications. We make many assumptions like those of the
EVM and provide a specification of a stablecoin.

## Structure

Specifications are formalized in files ending in `-spec.k`.

## Usage

To run, we recommend the docker version of the K-framework. Then to run the
commands in the `k` framework, you can do the following.

1. Checkout this repo somewhere.
1. Run `docker run -it -v /your-path-to-this-repo/hedera-stablecoin:/root/erc20 runtimeverificationinc/kframework-k:ubuntu-bionic-71d191f`
1. `cd root/erc20`
1. `kompile --backend java erc20.k`
1. `kprove compliant-spec.k` (or any other file ending in `-spec.k`)

It shold output `#True` (and maybe some warnings).

## Acknowledgments

Based on the [ERC-20 Formal Model](https://github.com/runtimeverification/erc20-semantics) of [Grigore Rosu](http://fsl.cs.illinois.edu/grosu).
