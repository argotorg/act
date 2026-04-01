# Act Metatheory Mechanization

Rocq mechanization of the metatheory of [Act](https://github.com/ethereum/act),
a specification language for Ethereum smart contracts.

The formalization covers the type system, pointer semantics, and type safety.
Value semantics and soundness are a work in progress. It follows the
formalization presented in the Act tech-report.

## Building

Requires [Rocq](https://rocq-prover.org/) >= 9.1.

```
make
```

## File Structure

The files are listed in dependency order:

| File | Description |
|------|-------------|
| `Maps.v` | Partial map library (identifiers, association lists, map inclusion) |
| `Syntax.v` | Types, expressions, references, and top-level constructs (contracts, constructors, transitions) |
| `Domains.v` | Semantic domains for pointer semantics: values, store, state, and environments |
| `Semantics.v` | Big-step operational semantics for pointer semantics |
| `ValueTyping.v` | Value typing, environment typing, entailment, and well-typed contract environments |
| `Typing.v` | Typing judgments for references, expressions, mappings, slots, creates, updates, constructors, transitions, and contracts |
| `TypeSafety.v` | Type safety: type preservation and progress lemmas for all syntactic categories |
| `TypingT.v` | Type-valued (`Type`) mirror of `Typing.v`, enabling large elimination for defining denotation functions |
| `ValueSemantics.v` | **(WIP)** Denotational value semantics: semantic domains of types and denotation functions mapping typed terms to Rocq values |
| `Soundness.v` | **(WIP)** Soundness of the value semantics with respect to the pointer semantics |
