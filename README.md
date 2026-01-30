# Act

Act is a formal specification language for constructing exhaustive, mathematically rigorous descriptions of EVM smart contracts.

Act specifications are written in a high-level, human-readable language that can be proved equivalent to EVM bytecode, currently via the [hevm](https://github.com/argotorg/hevm) symbolic execution engine.

Specifications can be extracted to a proof assistant (currently Rocq), accurately modeling contract behavior as a state transition system and enabling verification of complex properties and invariants.

The core vision of Act is to provide a provably correct mapping from EVM bytecode to a high-level mathematical model that can be embedded into a variety of analysis and verification tools.

In-depth documentation is available in [The Act Book](https://ethereum.github.io/act/).

Act builds on the previous [Act](https://github.com/dapphub/klab/blob/master/acts.md) project.


## Building

You can build the project with Nix. If you do not have Nix installed, try the [Determinate Nix installer](https://github.com/DeterminateSystems/nix-installer).

Build the `act` executable from the repository root:

```sh
nix build
```

This produces `bin/act`, which you can run as described in the Act Book.

For a quick overview of available options:

```sh
bin/act --help
```

## Developing

Enter a Nix shell with all dependencies installed:

```sh
nix develop
```

Then use `cabal` from the project root:

```sh
cabal build # build the project
cabal repl  # enter a repl
```

To execute unit tests:

```sh
make test      # run all tests
cabal v2-test  # run Haskell tests
```

To update project dependencies:

```sh
nix flake update
```

## Usage

Once you are in the Nix shell, you can use Act backends for `smt`, `hevm`, and `rocq` as follows:

```sh
cabal run act -- <OPTIONS>
```

Run the following command to see options and configuration flags:

```sh
cabal run act -- --help
```


## Getting Help

If you have questions, open an issue or reach out on our [Matrix Channel](https://matrix.to/#/#actlang:matrix.org).

The act development team is happy to help you use Act for smart contract verification.
