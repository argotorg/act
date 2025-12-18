# Specification Language Act

**to be edited**

At a very high level Act is a kind of mathy english over the EVM, where contracts are defined as a
set of pure functions taking a given EVM state (i.e. storage & blockchain context) and some calldata
and producing a new EVM state (`(EVM, Calldata) -> EVM`).

A specification of a contract written in Act consists of a constructor and a set of behaviours:

The constructor specification defines the structure of the contract’s state, the initial value of
the state, and a list of invariants that the contract should satisfy.

Each behaviour specification determines how a contract method updates the state, the method’s return
value (if any), and any conditions that must be satisfied in order for the state update to be
applied.

Alternatively, they can be thought of as an initial state and a set of state transitions,
determining an inductively defined state transition system.