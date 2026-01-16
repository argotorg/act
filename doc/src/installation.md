# Getting Started and Installation

## Getting Started

act uses Nix for dependency management and building. If you don't have Nix installed yet, you can use the [Determinate Nix installer](https://github.com/DeterminateSystems/nix-installer).

### Quick Start

To quickly try act without installing it, you can enter a Nix shell:

```sh
nix-shell https://github.com/argotorg/act/tarball/master
```

### Basic Usage

Once you are in the Nix shell or you have [installed act](./installation.md#building-from-source),
test your installation by running the `HelloWorld` contract specification:

The hevm backend:
```sh
cabal run act -- hevm --spec tests/helloworld/helloworld.act --sol tests/helloworld/helloworld.sol
```
(the output should conclude with `No discrepancies found.`)

The Rocq backend:
```sh
cabal run act -- rocq --file tests/helloworld/helloworld.act
```
(the output should conclude with `Qed. End HelloWorld.`)


Alternatively, if you've run `make` first, you can run the executable directly:

```sh
act <OPTIONS>
```

For advanced options, consult the
[hevm backend documentation](./equiv.md) and
[Rocq backend documentation](./rocq.md), 
or list the options by calling 
```sh
cabal run act -- --help
```

## Installation

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

Test your installation by running the commands in [basic usage section](#basic-usage).

Note: You can also use Cabal as normal from the root directory.
