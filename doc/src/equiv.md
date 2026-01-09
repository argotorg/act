# Checking equivalence with EVM bytecode

EVM bytecode can be formally verified to implement an Act spec. This
means that each successful behavior of the bytecode should be covered
by the Act spect. To check equivalence the Act spec is translated to
Expr, the intermediate representation of HEVM, and the EVM bytecode is
symbolically executed to obtain its Expr representation. Then
equivalence can be checked with the equivalence checker of HEVM.

The Expr representation of an Act program is a list of *Success*
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


## Equivalence checks 
To check equivalence between the two Expr representations the
following checks are performed. 

### Result equivalence
The two list of `Success` nodes are checked for equivalence using
the HEVM equivalence checker. For each pair of nodes in the two lists,
we check that for all inputs that satisfy the combined path conditions the
result and final storage the same. 

### Input space equivalence
Since the input space of the two lists is not necessarily exhaustive,
some inputs may lead to failed execution paths that are not
present in the list. We therefore need to check that the input space of the two
lists are the same. That is, there must not be inputs that satisfy
some path condition in the first list but not the second and vice verse. 

Say that the Act program has the Expr representation 
`[Success c1 r1 s1, ..., Success cn rn sn`
and the the EVM bytecode has the Expr representation 
`[Success c1' r1' s1', ..., Success cn' rn' sn'`

then we need to check that `c1 \/ .. \/ cn <-> c1' \/ .. \/ cn'` that
is, we require that `c1 \/ .. \/ cn /\ ~ (c1' \/ .. \/ cn')` and `c1'
\/ .. \/ cn' /\ ~ (c1 \/ .. \/ cn)` are both unsatisfiable.

### Exhaustiveness checks for bytecode
TODO


# Old Hevm Section

Act leverages the symbolic execution engine in hevm to provide a backend that can prove equivalence
between a contract specification and an implementation of that specification in EVM.

## Usage

To perform the equivalence proofs, you can simply run
```sh
act hevm --spec <PATH_TO_SPEC> --sol <PATH_TO_SOLIDITY_CODE>
```
 against your spec and runtime (solidity) code.

`act hevm` also accepts the following configuration flags:

- `--code TEXT`: runtime code.
- `--initcode TEXT`: initial code.
- `--solver`: you can choose to use `cvc5` or `z3` as the solver backend. The default is `cvc5`.
  Sometimes `cvc5` may be able to prove things that `z3` cannot (and vice versa). You can also
  prove the same properties with multiple solvers to gain confidence that the proofs are not
  affected by a bug in the solver itself.
- `--smttimeout`: the timeout (in milliseconds) given for each smt query. This is set to 20000 by default.
- `--debug`: this prints the raw query dispatched to the SMT solver to stdout.

## Description

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
that the contents of the return buffer matches what was specified in the transition’s returns block.

## Example

As an example, consider the following contract:

```
contract Simple {
    uint val;

    function set(uint x) external payable returns (uint) {
        require(x > 100);
        val = x;
        return x;
    }
}
```

We can represent this in Act as:

```
constructor of Simple
interface constructor()

creates

  uint val := 0
transition set of Simple
interface set(uint x)

iff

  x > 100

updates

  val => x

returns x
```

Act needs to have access to the storage layout metadata output by solc to compute the index in storage for each variable mentioned in the spec, so we need to pass a solc output json when trying to prove equivalence.

```
> act hevm --spec src/simple.act --soljson out/dapp.sol.json
checking postcondition...
Q.E.D.
Successfully proved set(Pass), 2 cases.
checking postcondition...
Q.E.D.
Successfully proved set(Fail), 2 cases.
==== SUCCESS ====
All transitions implemented as specified ∎.
```

If we try to prove equivalence of the spec and a faulty implementation like the one below:

```solidity
contract Simple {
    uint val;

    function set(uint x) external payable returns (uint) {
        require(x > 100);
        if (x == 2000) {
          val = x + 1;
        } else {
          val = x;
        }
        return x;
    }
}
```

Then Act will give us a counterexample showing a case where the implementation differs from the specification:

```
> act hevm --spec src/simple.act --soljson out/dapp.sol.json
checking postcondition...
Calldata:
0x60fe47b100000000000000000000000000000000000000000000000000000000000007d0
Caller:
0x0000000000000000000000000000000000000000
Callvalue:
0
Failed to prove set(Pass)
checking postcondition...
Q.E.D.
Successfully proved set(Fail), 2 cases.
==== FAILURE ====
1 out of 2 claims unproven:

1	Failed to prove set(Pass)
```