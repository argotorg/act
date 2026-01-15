# Layout and Tooling

## act Verification Pipeline

act provides two main verification backends that work with the same specification:

```
┌─────────────────────────────────────────────────────────────────┐
│                        act Specification                        │
│                   (High-level .act file)                        │
└────────────────┬───────────────────────────────┬────────────────┘
                 │                               │
                 │                               │
                 ▼                               ▼
    ┌────────────────────────┐      ┌──────────────────────────┐
    │    HEVM Backend        │      │     Rocq Backend         │
    │  (Automated Proofs)    │      │   (Manual Proofs)        │
    └────────────┬───────────┘      └──────────┬───────────────┘
                 │                             │
       ┌─────────┴─────────┐                   │
       │                   │                   │
       ▼                   ▼                   ▼
┌─────────────┐    ┌─────────────┐  ┌──────────────────────────┐
│  Solidity   │    │   Vyper     │  │  Transition System       │
│ .sol file   │    │  .vy file   │  │  Export to Rocq          │
└──────┬──────┘    └──────┬──────┘  └───────────┬──────────────┘
       │                  │                     │
       └────────┬─────────┘                     │
                ▼                               ▼
    ┌────────────────────────┐      ┌──────────────────────────┐
    │  Symbolic Execution    │      │ Interactive Theorem      │
    │  of EVM Bytecode       │      │ Proving (Gallina/Ltac)   │
    └────────────┬───────────┘      └──────────┬───────────────┘
                 │                             │
                 ▼                             │
    ┌────────────────────────┐                 │
    │ Equivalence Checking   │                 │
    │ Spec ≡ Implementation  │                 │
    │ (via SMT solvers)      │                 │
    └────────────┬───────────┘                 │
                 │                             │
                 ▼                             ▼
    Bytecode conforms              Higher-level properties
    to specification              proven about the spec
```

**HEVM Backend**: Automatically proves that EVM bytecode (compiled from Solidity or Vyper) correctly implements the act specification. It uses symbolic execution to explore all possible execution paths and SMT solvers (CVC5, Z3, or Bitwuzla) to verify equivalence.

**Rocq Backend**: Exports the specification as a formal transition system to the Rocq proof assistant (formerly Coq), enabling manual proofs of arbitrarily complex properties about the contract's behavior.

## Running the ERC20 Example

The act repository includes a complete ERC20 example that you can run with both verification backends. The example files are located in:
- `tests/hevm/pass/multisource/erc20/` - for HEVM backend examples
- `tests/coq/ERC20/` - for Rocq backend examples

### Verifying with HEVM Backend

The HEVM backend proves that the EVM bytecode implementation conforms to the act specification. You can verify the ERC20 specification against both Solidity and Vyper implementations.

**Verify against Solidity implementation:**

```sh
act hevm --spec tests/hevm/pass/multisource/erc20/erc20.act \
         --sol tests/hevm/pass/multisource/erc20/erc20.sol
```

**Verify against Vyper implementation:**

```sh
act hevm --spec tests/hevm/pass/multisource/erc20/erc20.act \
         --vy tests/hevm/pass/multisource/erc20/erc20.vy
```

The `--spec` flag specifies the act specification file, while `--sol` or `--vy` point to the corresponding implementation. The HEVM backend will:
1. Compile the source code to EVM bytecode
2. Symbolically execute the bytecode
3. Check equivalence between the specification and implementation
4. Report success or provide counterexamples if differences are found

#### Expected Output

When verification succeeds, you should see output similar to this:

```
Checking IFF constructor
[HEVM] Running pass for constructor...
[HEVM] Running fail for constructor...

Checking IFF transfer
[HEVM] Running pass for transfer...
checking postcondition...
Q.E.D.
Successfully proved transfer(Pass), 3 cases.
[HEVM] Running fail for transfer...
checking postcondition...
Q.E.D.
Successfully proved transfer(Fail), 2 cases.

Checking IFF transferFrom
[HEVM] Running pass for transferFrom...
checking postcondition...
Q.E.D.
Successfully proved transferFrom(Pass), 4 cases.
[HEVM] Running fail for transferFrom...
checking postcondition...
Q.E.D.
Successfully proved transferFrom(Fail), 3 cases.

Checking IFF approve
[HEVM] Running pass for approve...
checking postcondition...
Q.E.D.
Successfully proved approve(Pass), 2 cases.
[HEVM] Running fail for approve...
checking postcondition...
Q.E.D.
Successfully proved approve(Fail), 1 cases.

==== SUCCESS ====
All transitions implemented as specified ∎.
```

**What this output means:**

- Each transition (function) in your specification is checked separately
- For each transition, two claims are verified:
  - **Pass claim**: When preconditions are met, the implementation correctly updates storage and returns the expected value
  - **Fail claim**: When preconditions are not met, the implementation reverts
- **"Q.E.D."** indicates the SMT solver successfully proved the property
- **"X cases"** shows how many execution paths were verified
- **"SUCCESS"** confirms all transitions match the specification

#### When Verification Fails

If the implementation doesn't match the specification, act provides a counterexample:

```
Checking IFF transfer
[HEVM] Running pass for transfer...
checking postcondition...
Calldata:
0xa9059cbb000000000000000000000000000000000000000000000000000000000000dead0000000000000000000000000000000000000000000000000000000000000064
Caller:
0x000000000000000000000000000000000000c0de
Callvalue:
0

Storage:
└> 0x0...01 ↦ 0x0...200  -- balanceOf[CALLER] = 512
└> 0x0...02 ↦ 0x0...100  -- totalSupply = 256

Failed to prove transfer(Pass)

==== FAILURE ====
1 out of 8 claims unproven:

1	Failed to prove transfer(Pass)
```

This counterexample shows:
- The specific **calldata** that triggers the mismatch
- The **caller** address
- The **callvalue** (ETH sent)
- The **storage state** where the issue occurs
- Which **claim failed**

You can use this information to debug either your specification or implementation.

#### Additional Verification Options

You can also use additional flags:
- `--solver <cvc5|z3|bitwuzla>` - choose the SMT solver (default: cvc5)
- `--smttimeout <ms>` - set timeout for SMT queries (default: 20000ms)
- `--debug` - print the raw SMT queries for debugging

**Note:** The `--sources` flag can alternatively be used with a JSON configuration file that specifies multiple contracts and their sources, which is useful for more complex projects with multiple interacting contracts.

### Generating Rocq Proofs

The Rocq backend exports the act specification to the Rocq proof assistant, enabling manual proofs of higher-level properties.

**Generate Rocq code:**

```sh
act rocq --file tests/coq/ERC20/erc20.act
```

This command generates a `.v` file containing the formalization of the ERC20 specification in Rocq's Gallina language. The generated file includes:
- Type definitions for the contract state
- Transition functions for each transition
- Predicates encoding preconditions and postconditions

**Compile and verify Rocq proofs:**

After generating the Rocq code, you can build and verify custom proofs about the specification:

```sh
cd tests/coq/ERC20
make
```

The `ERC20/` directory includes:
- `erc20.act` - the act specification
- `ERC20.v` - generated Rocq formalization
- `Theory.v` - custom theorems and proofs about the ERC20 contract
- `Makefile` and `_CoqProject` - build configuration

You can open the `.v` files in your Rocq IDE (such as CoqIDE or Proof General) to interactively explore and extend the proofs.

## Backend Reference Guide

This section provides comprehensive documentation for all command-line options and usage patterns for act's verification backends.

### HEVM Backend - Complete Reference

The HEVM backend performs automated equivalence checking between act specifications and EVM bytecode implementations.

#### Basic Usage Patterns

**1. Single contract with Solidity:**
```sh
act hevm --spec <PATH_TO_SPEC> --sol <PATH_TO_SOL>
```

**2. Single contract with Vyper:**
```sh
act hevm --spec <PATH_TO_SPEC> --vy <PATH_TO_VY>
```

**3. Direct bytecode verification:**
```sh
act hevm --spec <PATH_TO_SPEC> --code <RUNTIME_BYTECODE> --initcode <CONSTRUCTOR_BYTECODE>
```

**4. Multi-contract projects:**
```sh
act hevm --sources <PATH_TO_CONFIG_JSON>
```

#### HEVM Command-Line Flags

| Flag | Type | Default | Description |
|------|------|---------|-------------|
| `--spec` | Path | - | Path to the act specification file (.act) |
| `--sol` | Path | - | Path to Solidity source file (.sol) |
| `--vy` | Path | - | Path to Vyper source file (.vy) |
| `--code` | ByteString | - | Runtime bytecode (hexadecimal) for direct verification |
| `--initcode` | ByteString | - | Constructor bytecode (hexadecimal) |
| `--sources` | Path | - | Path to JSON configuration file for multi-contract projects |
| `--solver` | `cvc5\|z3\|bitwuzla` | `cvc5` | SMT solver to use for verification |
| `--smttimeout` | Integer (ms) | `20000` | Timeout for each SMT query in milliseconds |
| `--debug` | Boolean | `false` | Print verbose output including raw SMT queries |

#### Using the --sources Flag for Multi-Contract Projects

For projects with multiple contracts or contracts that interact with each other, use a JSON configuration file:

**JSON Structure:**
```json
{
  "specifications": ["contract1.act", "contract2.act"],
  "sources": {
    "Token.sol": { "language": "Solidity" },
    "Vault.vy": { "language": "Vyper" }
  },
  "contracts": {
    "Token": { "source": "Token.sol" },
    "Vault": { "source": "Vault.vy" }
  }
}
```

**Example:**
```sh
act hevm --sources project.json --solver bitwuzla --smttimeout 60000
```

#### Direct Bytecode Verification

When you already have compiled bytecode (e.g., from Foundry, Hardhat, or other tools):

```sh
act hevm --spec mycontract.act \
         --code 0x608060405234801... \
         --initcode 0x608060405234801... \
         --solver z3
```

This is useful for:
- Verifying optimized or custom-compiled bytecode
- Integration with other build tools
- Verifying bytecode from block explorers

#### Solver Selection Strategies

Different solvers have different strengths:

- **CVC5** (default): Good all-around performance, handles most common contracts
- **Z3**: Alternative when CVC5 times out; sometimes faster on arithmetic-heavy specs
- **Bitwuzla**: Specialized for bitvector reasoning; excellent for bitwise operations

**Tip:** For critical contracts, run verification with multiple solvers:
```sh
act hevm --spec contract.act --sol contract.sol --solver cvc5
act hevm --spec contract.act --sol contract.sol --solver z3
act hevm --spec contract.act --sol contract.sol --solver bitwuzla
```

#### Debugging Failed Proofs

When verification fails, use the `--debug` flag to see the SMT queries:

```sh
act hevm --spec contract.act --sol contract.sol --debug
```

This outputs:
- The symbolic execution trace
- Path conditions
- Storage constraints
- Raw SMT queries sent to the solver
- Counterexamples when equivalence fails

### Rocq Backend - Complete Reference

The Rocq backend exports act specifications to the Rocq proof assistant for manual theorem proving.

#### Basic Usage

**Generate Rocq formalization:**
```sh
act rocq --file <PATH_TO_SPEC>
```

This creates a `.v` file containing:
- Gallina type definitions for contract state
- Transition functions for each transition
- Precondition and postcondition predicates
- Storage update functions

#### Rocq Command-Line Flags

| Flag | Type | Default | Description |
|------|------|---------|-------------|
| `--file` | Path | - | Path to the act specification file (.act) |
| `--solver` | `cvc5\|z3` | `cvc5` | SMT solver used during spec analysis |
| `--smttimeout` | Integer (ms) | `20000` | Timeout for SMT queries during analysis |
| `--debug` | Boolean | `false` | Print verbose output during generation |

#### Setting Up a Rocq Project

After generating the `.v` file, you need to set up a proper Rocq project structure. act's Rocq backend generates code that depends on the ActLib library, which provides foundational definitions for reasoning about EVM contracts.

**Project Structure:**
```
my-contract/
├── _CoqProject          # Rocq project configuration
├── Makefile             # Build automation
├── mycontract.act       # Your act specification
├── MyContract.v         # Generated (by act rocq)
└── Theory.v             # Your custom proofs
```

**1. Create a `_CoqProject` file:**

The `_CoqProject` file tells Rocq where to find dependencies and which files to compile:

```coq-project
-Q . MyContractName
-Q /path/to/act/lib ActLib

/path/to/act/lib/ActLib.v
MyContract.v
Theory.v
```

**Explanation:**
- `-Q . MyContractName` - Maps current directory to the logical name `MyContractName`
- `-Q /path/to/act/lib ActLib` - Makes ActLib available (adjust path to your act installation)
- List all `.v` files that should be compiled

**For the ERC20 example in the act repository:**
```coq-project
-Q . ERC20
-Q ../../../lib ActLib

../../../lib/ActLib.v
ERC20.v
Theory.v
```

**2. Create a `Makefile`:**

This Makefile automates the entire workflow from act spec to verified proofs:

```makefile
.PHONY: verify
verify: RocqMakefile MyContract.v
	make -f RocqMakefile

MyContract.v: mycontract.act
	act coq --file mycontract.act > MyContract.v

RocqMakefile: _CoqProject
	rocq makefile -f _CoqProject -o RocqMakefile

.PHONY: clean
clean:
	if [[ -f RocqMakefile ]]; then make -f RocqMakefile clean; fi
	rm -f MyContract.v RocqMakefile RocqMakefile.conf
	rm -f *.glob *.vo *.vok *.vos .*.aux

.PHONY: regenerate
regenerate: clean MyContract.v verify
```

**Makefile Targets Explained:**

- **`make verify`** (or just `make`) - Full build pipeline:
  1. Generates `MyContract.v` from your `.act` file if needed
  2. Creates `RocqMakefile` from `_CoqProject`
  3. Compiles all Rocq files and checks proofs

- **`make clean`** - Removes all generated and compiled files:
  - Generated `.v` file
  - Compiled Rocq artifacts (`.vo`, `.vok`, `.vos`, `.glob`)
  - Makefile artifacts

- **`make regenerate`** - Clean rebuild from scratch


**3. Write custom proofs in `Theory.v`:**

Start with the basic structure:

```coq
Require Import MyContract.
Require Import ActLib.

(* Import generated definitions *)
Import MyContract.

(* Example: Prove an invariant about the contract *)
Theorem total_supply_invariant : forall state input state',
  transition state input = Some state' ->
  total_supply state = total_supply state'.
Proof.
  intros state input state' Htrans.
    (* Proof by case analysis on the transition *)
    (* ... proof steps ... *)

Qed.
```

**4. Build and verify:**

```sh
# Initial build (generates .v file and compiles everything)
make verify

# After modifying Theory.v, just rebuild
make -f RocqMakefile

# After modifying the .act spec, regenerate
make regenerate
```

#### Interactive Proof Development

Use Rocq IDEs for interactive proof construction:

**VS Code with VsCoq:**
Install the VsCoq extension and open `.v` files.

**CoqIDE:**
```sh
coqide Theory.v
```

**Emacs with Proof General:**
```elisp
; In your .emacs file:
(load-file "~/.emacs.d/lisp/PG/generic/proof-site.el")
```


### General Help and Documentation

**Getting help:**
```sh
act --help              # General help
act hevm --help         # HEVM-specific help
act rocq --help         # Rocq-specific help
```

