# Installation

## Install Nix
Act uses Nix for dependency management and building. If you don't have Nix installed yet, you can use the [Determinate Nix installer](https://github.com/DeterminateSystems/nix-installer).

## Quick Start

To quickly try Act without installing it, you can enter a Nix shell:

```sh
nix-shell https://github.com/argotorg/act/tarball/master
```

Test your installation by running the following command:
<span style="color:red">Change to a hello world example</span>

```sh
cabal run act -- --help
```

## Building from Source

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
## Usage 
Consult the [Getting Started](./part1.md#getting-started) section for more information on using Act.