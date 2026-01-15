# What is act?
act is a formal specification language and verification framework for proving the correctness of Ethereum Virtual Machine (EVM) smart contracts. act specifications precisely describe all possible behaviors of a smart contract in a high-level language and are automatically verified against the contract’s EVM bytecode using symbolic execution. 

## Getting Started

act uses Nix for dependency management and building. If you don't have Nix installed yet, you can use the [Determinate Nix installer](https://github.com/DeterminateSystems/nix-installer).

### Quick Start

To quickly try act without installing it, you can enter a Nix shell:

```sh
nix-shell https://github.com/argotorg/act/tarball/master
```

### Basic Usage

Test your installation by running the following command:
<span style="color:red">Change to a hello world example</span>

```sh
cabal run act -- --help
```

Once are in the Nix shell or you have [installed act](./installation.md#building-from-source), you can use act backends for `rocq` and `hevm`:

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




## Installation

### Install Nix
act uses Nix for dependency management and building. If you don't have Nix installed yet, you can use the [Determinate Nix installer](https://github.com/DeterminateSystems/nix-installer).

### Quick Start

To quickly try act without installing it, you can enter a Nix shell:

```sh
nix-shell https://github.com/argotorg/act/tarball/master
```

Test your installation by running the following command:
<span style="color:red">Change to a hello world example</span>

```sh
cabal run act -- --help
```

### Building from Source

1. Clone the repository:
```sh
git clone https://github.com/argotorg/act.git
cd act
```

2. Build the project:
```sh
nix build
```

Once you have built, for development, enter a Nix development shell to get all dependencies:

```sh
nix develop
```

Test your installation by running the following command:
<span style="color:red">Change to a hello world example</span>

```sh
cabal run act -- --help
```

You can then use Cabal as normal from the root directory:

```sh
cabal build # build
cabal repl  # enter a repl instance
```
### Usage 
Consult the [Getting Started](./part1.md#getting-started) section for more information on using act.
