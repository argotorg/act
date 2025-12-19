# Practical Usage

## Getting Started

### Installation

Act uses Nix for dependency management and building. If you don't have Nix installed yet, you can use the [Determinate Nix installer](https://github.com/DeterminateSystems/nix-installer).

#### Quick Start

To quickly try Act without installing it, you can enter a Nix shell:

```sh
nix-shell https://github.com/argotorg/act/tarball/master
```

#### Building from Source

1. Clone the repository:
```sh
git clone https://github.com/argotorg/act.git
cd act
```

2. Build the project:
```sh
nix build
```

#### Development Setup

For development, enter a Nix development shell to get all dependencies:

```sh
nix develop
```

Then use Cabal as normal from the root directory:

```sh
cabal build # build
cabal repl  # enter a repl instance
```

### Basic Usage

Once you have Act installed or are in the Nix shell, you can use Act backends for `smt`, `hevm`, and `rocq`:

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
