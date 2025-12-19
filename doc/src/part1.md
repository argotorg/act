# What is Act?
<!-- paper abstract -->
Act is a formal specification language and verification framework for proving the correctness of Ethereum Virtual Machine (EVM) smart contracts. Act specifications precisely describe all possible behaviors of a smart contract in a high-level language and are automatically verified against the contract’s EVM bytecode using symbolic execution. 

## Getting Started

Act uses Nix for dependency management and building. If you don't have Nix installed yet, you can use the [Determinate Nix installer](https://github.com/DeterminateSystems/nix-installer).

### Quick Start

To quickly try Act without installing it, you can enter a Nix shell:

```sh
nix-shell https://github.com/argotorg/act/tarball/master
```

### Basic Usage

Test your installation by running the following command:
<span style="color:red">Change to a hello world example</span>

```sh
cabal run act -- --help
```

Once are in the Nix shell or you have [installed Act](./installation.md#building-from-source), you can use Act backends for `rocq` and `hevm`:

```sh
cabal run act -- <OPTIONS>
```

To see all available options and configuration flags:

```sh
cabal run act -- --help
```

Alternatively, if you've run `make` first, you can run the executable directly:

```sh
act <OPTIONS>
```

## Documentation Structure


This documentation is structured in the following way.
1. The current section **What is Act?** provides a high-level description of the key idea of act together with its features. It further introduces the ERC20 token contract, which will be used as example throughout this documentation.
2. **Specification Language Act** introduces the building blocks of act as a specification language. The respective subchapters focus on various components.
3. The section **From Specification to Guarantees** shows how act can be used to prove that the spec complies with its implementation and how to formally prove further properties about the contract via its act spec.
4. **Advanced Topics** discusses certain design choices.
5. Finally, in **Practical Usage** it is explained how to get started with act including instructions on installation and writing you own spec.