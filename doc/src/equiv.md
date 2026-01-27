# hevm Backend: Checking Equivalence with EVM Bytecode

**Table of Contents**

- [Usage](#usage)
  - [Basic Usage Patterns](#basic-usage-patterns)
  - [Command-Line Flags](#command-line-flags)
  - [Running the ERC20 Example](#running-the-erc20-example)
  - [Expected Output for Successful Verification](#expected-output-for-successful-verification)
  - [When Verification Fails: Example with Broken ERC20](#when-verification-fails-example-with-broken-erc20)
  - [Verifying Multiple Contracts with --sources](#verifying-multiple-contracts-with---sources)
  - [Additional Options](#additional-options)
- [How it works](#how-it-works)
  - [Success nodes](#success-nodes)
  - [Equivalence check](#equivalence-check)

---

EVM bytecode can be formally verified to implement an act spec. This
means that each successful behavior of the bytecode should be covered
by the act spec and vice-versa. 

To check equivalence, act leverages the symbolic execution engine in hevm.
The act spec is translated to
Expr, the intermediate representation of hevm, and the EVM bytecode is
symbolically executed to obtain its Expr representation. Then
equivalence can be checked with the equivalence checker of hevm.

## Usage 

The hevm backend performs automated equivalence checking between act specifications and EVM bytecode implementations.
It is language agnostic, currently (version 0.2.0) supporting verification of contracts written in both Solidity and Vyper.

### Basic Usage Patterns

**1. Single contract with Solidity:**
```sh
act hevm --spec <PATH_TO_SPEC> --sol <PATH_TO_SOL>
```

**2. Single contract with Vyper:**
```sh
act hevm --spec <PATH_TO_SPEC> --vy <PATH_TO_VY>
```

**3. Multi-contract projects:** (more info in [Multi-Contract Projects](#verifying-multiple-contracts-with---sources))
```sh
act hevm --sources <PATH_TO_CONFIG_JSON>
```

<!-- **4. Direct bytecode verification:**
```sh
act hevm --spec <PATH_TO_SPEC> --code <RUNTIME_BYTECODE> --initcode <CONSTR_BYTECODE>
``` -->

### Command-Line Flags

| Flag | Type | Default | Description |
|------|------|---------|-------------|
| `--spec` | Path | - | Path to the act specification file (.act) |
| `--sol` | Path | - | Path to Solidity source file (.sol) |
| `--vy` | Path | - | Path to Vyper source file (.vy) |
| `--sources` | Path | - | Path to JSON configuration file for multi-contract projects |
| `--solver` | `cvc5\|z3\|bitwuzla` | `cvc5` | SMT solver to use for verification |
| `--smttimeout` | Integer (ms) | `20000` | Timeout for each SMT query in milliseconds |
| `--debug` | Boolean | `false` | Print verbose output including raw SMT queries |

<!-- | `--code` | ByteString | - | Runtime bytecode (hexadecimal) for direct verification | -->
<!-- | `--initcode` | ByteString | - | Constructor bytecode (hexadecimal) | -->

### Running the ERC20 Example

The act repository includes a complete ERC20 example demonstrating equivalence checking. The example files are located in `tests/hevm/pass/multisource/erc20/`.

**Verify ERC20 against Solidity implementation:**

```sh
act hevm --spec tests/hevm/pass/multisource/erc20/erc20.act \
         --sol tests/hevm/pass/multisource/erc20/erc20.sol
```

**Verify ERC20 against Vyper implementation:**

```sh
act hevm --spec tests/hevm/pass/multisource/erc20/erc20.act \
         --vy tests/hevm/pass/multisource/erc20/erc20.vy
```

The hevm backend will:
1. Compile the source code to EVM bytecode
2. Symbolically execute the bytecode
3. Check equivalence between the specification and implementation
4. Report success or provide counterexamples if differences are found

### Expected Output for Successful Verification

When the ERC20 implementation matches its specification, you should see output similar to this:

```
Checking contract Token
No discrepancies found. 
Checking if constructor results are equivalent.
Found 1 total pairs of endstates
Asking the SMT solver for 1 pairs
No discrepancies found. 
Checking if constructor input spaces are the same.
No discrepancies found. 
Checking transition transfer of act
Checking if behaviour is matched by EVM
Found 2 total pairs of endstates
Asking the SMT solver for 2 pairs
No discrepancies found. 
Checking if the input spaces are the same
No discrepancies found. 
...
Checking transition allowance of act
Checking if behaviour is matched by EVM
Found 1 total pairs of endstates
Asking the SMT solver for 1 pairs
No discrepancies found. 
Checking if the input spaces are the same
No discrepancies found. 
Checking if the ABI of the contract matches the specification
No discrepancies found. 
```

**Understanding the output:**

Consult the [how it works](#how-it-works) section for more details.
- **Checking contract Token**: Initial verification that the contract structure is valid
- **Checking if constructor results are equivalent**: Verifies that the constructor in the implementation produces the same storage state as the act specification
- **Found X total pairs of endstates**: The number of distinct execution paths (success nodes, see [here](#success-nodes)) that were identified during symbolic execution
- **Asking the SMT solver for X pairs**: How many queries are sent to the SMT solver to verify equivalence between corresponding endstates
- **No discrepancies found**: The SMT solver confirmed that for all inputs satisfying the path conditions, the results and storage are identical between specification and implementation
- **Checking if the input spaces are the same**: Verifies that both the act spec and EVM implementation accept and reject the same set of inputs (no missing cases), see [here](#input-space-equivalence)
- **Checking if the ABI of the contract matches the specification**: Ensures all function signatures match between the specification and implementation

**What each transition check involves:**
1. **Checking transition X of act**: Start verification of a specific function
2. **Checking if transition is matched by EVM**: Confirm the EVM implementation has corresponding behavior
3. **Endstate equivalence**: For each execution path, verify that when the same inputs are provided:
   - Storage updates are identical
   - Return values are identical
   - Both succeed or both revert
4. **Input space equivalence**: Verify that the sets of inputs that succeed (or fail) are the same in both spec and implementation

### When Verification Fails: Example with Broken ERC20

If the implementation doesn't match the specification, act provides a detailed counterexample. Consider a faulty ERC20 implementation where `transfer` incorrectly updates balances:

```solidity
// Broken implementation
    function transfer(uint256 value, address to) public returns (bool) {
        require(balanceOf[msg.sender] >= value);
        if (to == address(0xdead)) {
            balanceOf[msg.sender] = balanceOf[msg.sender] - value;
            balanceOf[to] = balanceOf[to] + value + 1;  // Bug: adds extra token!
        } else {
            balanceOf[msg.sender] = balanceOf[msg.sender] - value;
            balanceOf[to] = balanceOf[to] + value;
        }
        return true;
    }
```

Running verification on this broken implementation produces:

```
Checking behavior transfer of act
Checking if behaviour is matched by EVM
Found 4 total pairs of endstates
Asking the SMT solver for 4 pairs
Not equivalent.

-----

The following input results in different behaviours
Calldata:
  transfer(0,0x000000000000000000000000000000000000dEaD)
Storage:
  Addr SymAddr "entrypoint": [(0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe),(0x8000000000000000000000000000000000000000000000000000000000000001,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)]
Transaction Context:
  TxValue: 0x0
Addrs:
  SymAddr "caller": 0xFF0000000000000000000000000000000000DEAD
  SymAddr "to": 0x000000000000000000000000000000000000dEaD
```

**Interpreting the counterexample:**

- **Calldata**: The specific function call that triggers the bug: `transfer(0, 0x000000000000000000000000000000000000dEaD)` - transferring 0 tokens to address `0xdead`
- **Storage**: The contract state where the discrepancy occurs. The storage shows:
  - Key-value pairs in hexadecimal representing storage slots
  - `0x7fff...f01 ↦ 0xfff...ffe`: Storage location and its value
  - `0x8000...001 ↦ 0xfff...fff`: Another storage location (likely total supply or balance)
- **Transaction Context**: 
  - `TxValue: 0x0` - No ETH sent with the call (0 wei)
- **Addrs**: The symbolic addresses involved:
  - `SymAddr "caller": 0xFF...DEAD` - The address executing the transaction
  - `SymAddr "to": 0x000...dEaD` - The recipient address


This counterexample tells us that transferring 0 tokens to address `0xdead` produces different results in the implementation versus the specification, allowing developers to locate and fix the bug.

### Verifying Multiple Contracts with --sources

For complex projects with multiple interacting contracts, use a JSON configuration file, that might look like this:

**JSON Structure (`project.json`):**
```json
{
  "specifications": ["<path-to-spec1>/spec1.act", "<path-to-spec2>/spec2.act"],
  "sources": {
    "<path-to-source1>/source1.sol": { "language": "Solidity" },
    "<path-to-source2>/source2.vy": { "language": "Vyper" },
    "<path-to-source3>/source3.vy": { "language": "Vyper" }
  },
  "contracts": {
    "Contract1": { "source": "<path-to-source1>/source1.sol" },
    "Contract2": { "source": "<path-to-source2>/source2.vy" },
    "Contract3": { "source": "<path-to-source3>/source3.vy" },
    "Contract4": { "source": "<path-to-source3>/source3.vy" }
  }
}
```

**Fields explained:**
- `specifications`: Array of act specification files
- `sources`: Map of source files to their language (Solidity or Vyper)
- `contracts`: Map of contract names to their source files

Note that specifications and sources may contain multiple contracts.

**Running verification:**
```sh
act hevm --sources project.json --solver bitwuzla --smttimeout 60000
```

**Example: Automatic Market Maker (AMM) with Solidity and Vyper:**

The act repository includes an example with mixed languages in `tests/hevm/pass/multisource/amm/`:

```json
{
  "specifications" : ["amm.act", "../erc20/erc20.act"],
  "sources" : {
    "../erc20/erc20.vy" : { "language" : "Vyper" },
    "amm.sol" : { "language" : "Solidity" }
  },
  "contracts" : {
    "Token" : { "source" : "../erc20/erc20.vy"},
    "Amm" : { "source" : "amm.sol"}
  }
}
```

This allows verification of specifications against implementations in different languages, and verification of multiple contracts that interact with each other.

### Additional Options

**Choosing SMT solvers:**

Different solvers have different strengths:
- **CVC5** (default): Good all-around performance, handles most common contracts
- **Z3**: Alternative when CVC5 times out; sometimes faster on arithmetic-heavy specs
- **Bitwuzla**: Specialized for bitvector reasoning; excellent for bitwise operations

```sh
act hevm --spec contract.act --sol contract.sol --solver z3
```

**Debugging failed proofs:**

Use the `--debug` flag to see detailed SMT queries:

```sh
act hevm --spec contract.act --sol contract.sol --debug
```

This outputs:
- The symbolic execution trace
- Path conditions
- Storage constraints
- Raw SMT queries sent to the solver
- Detailed counterexamples when equivalence fails

## How it works

### Success nodes

The Expr representation of an act program is a list of *Success*
nodes, that contain the possible successful results of the
computation. The Expr representation of the EVM bytecode can also be
flattened to a list of result nodes from which we only keep the
successful executions, filtering out failed and partial execution
paths. An informative warning will be thrown when partial executions
are encountered.

A success node in Expr, `Success cond res storage`, is a leaf in the
Expr tree representation and contains the path conditions, `cond` that
lead to the leaf, the result buffer `res`, and the end state
`storage`.

In order to compute the index in storage for each variable mentioned in the spec, 
act needs to have access to the 
storage layout metadata output by the compiler. 
<!-- Therefore we need to pass a solc output json when trying to prove equivalence. -->


### Equivalence check

To check equivalence between the two Expr representations the
following checks are performed. 

#### Result equivalence
The two lists of `Success` nodes are checked for equivalence using
the hevm equivalence checker. For each pair of nodes in the two lists,
we check that for all inputs that satisfy the combined path conditions the
result and final storage are the same. 

In act v0.2.0 the order of creating new contracts is relevant. 
Writing 
```act
A a := new A()
B b := new B()
```
is not equivalent to 
```act
B b := new B()
A a := new A()
```
as the pointers to the contract storage are not the same. The order of contract creation
must match the one in the EVM bytecode for the equivalence checker to succeed.
This restriction might be lifted in later releases of act.

#### Input space equivalence

We also need to check that the EVM bytecode implementation and act specification
revert at the same inputs.
Since the input space of the two lists is not necessarily exhaustive,
some inputs may lead to failed execution paths that are not
present in the list. We therefore need to check that the input space of the two
lists are the same. That is, there must not be inputs that satisfy
some path condition in the first list but none the second and vice versa.

Say that the act program has the Expr representation 

`Success c1 r1 s1, ..., Success cn rn sn`

and the the EVM bytecode has the Expr representation 

`Success c1' r1' s1', ..., Success cn' rn' sn'`

then we need to check that
 `c1 ∨ .. ∨ cn ⟺ c1' ∨ .. ∨ cn'` that
is, we require that 

`c1 ∨ .. ∨ cn ∧ ¬(c1' ∨ .. ∨ cn')` and
 `c1' ∨ .. ∨ cn' ∧ ¬(c1 ∨ .. ∨ cn)`

 are both unsatisfiable.

#### Exhaustiveness checks for bytecode

The hevm backend performs public interface matching between the EVM bytecode implementation and the act specification. 
It verifies that each contract defines the same constructor and the same set of transitions, with matching function signatures.

<!-- Old descritpion -->
<!-- ## Description

Two claims are generated for each transition, Pass and Fail. The Pass claim states that if all
preconditions in the iff block are true, then all executions will succeed, storage will be updated
according to the storage block, and the specified return value will, in fact, be returned. The Fail
claim states that should any of the preconditions be false, all executions will revert.

In both cases we begin the proof by constraining calldata to be of the form specified in the
transitions’ interface blocks, as well as making the relevant assumptions depending on whether the
claim is Pass or Fail, and then symbolically executing the bytecode object with storage held to be
completely abstract.

This produces a tree of potential executions where each node represents a potential branching point,
and each leaf represents a possible final state of the contract after the execution of a single
call.

In the case of a Fail claim, we can then check that each leaf represents a state in which execution
has reverted, while for a Pass claim we can check that storage has been updated as expected, and
that the contents of the return buffer matches what was specified in the transition’s returns block. -->

