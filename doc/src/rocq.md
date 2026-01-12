# Rocq

In order to reason about the contracts and prove their properties, the Rocq backend of Act shallowly 
embeds the Act specification into the logic of the Rocq proof assistant.

For this embedding to be sound, we ensure that the storage of the
contract (and the contracts reachable from it) satisfies the *unique ownership invariant* (see [aliasing section](./aliasing.md)), meaning that its storage may never contain any aliased references to other contracts.
Act checks this invariant automatically immediately after the type-checking phase.

A proof assistant provides tools that help to construct proofs. Rocq, in particular, is highly
interactive. The user typically builds proofs step by step, with the software giving feedback as the
proof progresses.

The requirements on proofs in a system like Rocq, Isabelle, or Lean are quite strict. These tools
only accept proofs that are algorithmically verifiable to be valid series of applications of the
system’s inference rules. This is generally stricter than what is typically expected of pen and
paper proofs, which often omit tedious details in the interest of clarity and concision.

The verification of these proofs is performed in a minimal and well-audited kernel. Although
occasionally bugs have been found in Rocq’s and other systems’ kernels, a proof in these systems is
generally quite strong evidence of correctness.

## Usage

**Generate Rocq formalization:**
To generate the Rocq code run
```sh
act rocq --file <PATH_TO_SPEC>
```
against your spec.

#### Rocq Command-Line Flags

| Flag | Type | Default | Description |
|------|------|---------|-------------|
| `--file` | Path | - | Path to the Act specification file (.act) |
| `--solver` | `cvc5\|z3` | `cvc5` | SMT solver used during type-checking and unique ownership verification |
| `--smttimeout` | Integer (ms) | `20000` | Timeout for SMT queries |
| `--debug` | Boolean | `false` | Print verbose output during generation |


#### Setting Up a Rocq Project

To fully use this feature you should also set up a `Makefile` and `_RocqProject`. Following the example in `tests/rocq/ERC20/`, 
the project structure should look something like this:
```
my-contract/
├── mycontract.act       # Your Act specification
├── MyContract.v         # Generated (by act rocq)
├── _RocqProject         # Rocq project configuration
├── Makefile             # Build automation
└── Theory.v             # Your custom proofs
```

Act's Rocq backend generates code that depends on the ActLib library, which provides foundational definitions for reasoning about EVM contracts. It should be included in your Rocq project.

**1. Create a `_RocqProject` file:**

The `_RocqProject` file tells Rocq where to find dependencies and which files to compile:

```coq-project
-Q . MyContractName
-Q /path/to/act/lib ActLib

/path/to/act/lib/ActLib.v
MyContract.v
Theory.v
```

**Explanation:**
- `-Q . MyContractName` - Maps current directory to the logical name `MyContractName`
- `-Q /path/to/act/lib ActLib` - Makes ActLib available (adjust path to your Act installation)
- List all `.v` files that should be compiled

**For the ERC20 example in the Act repository:**
```coq-project
-Q . ERC20
-Q ../../../lib ActLib

../../../lib/ActLib.v
ERC20.v
Theory.v
```

**2. Create a `Makefile`:**

This Makefile automates the entire workflow from Act spec to verified proofs:

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

(* Prove invariants and properties about the contract *)
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

If you are using Rocq in your editor in an interactive mode, make sure your editor links to the Rocq executables (rocqtop) from the nix shell.
Alternatively you can use a local Rocq executable, if present, and `make` outside of the nix shell, once the `act rocq` command has terminated.

## A Brief Introduction to Proof in Rocq

Rocq is a complex system with a steep learning curve, and while a full tutorial on programming in Rocq
is out of the scope of this blog post, we can give a little taste of how things work. For a more
thorough introduction, the books Software Foundations and Certified Programming With Dependent Types
are both excellent. Software Foundations in particular is a great introduction for users with little
experience in the fields of formal logic and proof theory.

The Rocq system is composed of three languages: a minimal functional programming language (Gallina),
a tactics language for proof construction (Ltac), and a “vernacular” for interaction with the
kernel. Let’s start with the very basics: defining the natural numbers and proving something about
addition.

We start by defining the type of natural numbers. There are infinitely many natural numbers, so of
course they must be defined inductively. In fact, all type definitions are done with the Inductive
vernacular command, even if they are not in fact inductive. Rocq’s Inductive is analogous to
Haskell’s data and OCaml’s type (with the added power of dependent types).

We define two constructors: `O`, representing 0, and `S`, which when applied to the natural number n
produces the representation of the number `n + 1` (S as in "successor"). To give a concrete example, 3
would be represented in this encoding as `S (S (S 0)))` i.e `1 + (1 + (1 + 0))`.

```Rocq
Inductive nat : Type :=
  | O
  | S (n : nat).
```

This is an example of a unary number representation. It can often be helpful to represent numbers
this way, since the inductive nature of the definition lends itself to inductive proof techniques.

Let’s continue by defining addition over our nat type:

```Rocq
Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O ⇒ m
  | S n' ⇒ S (plus n' m)
  end.
```

Here we define a recursive function (a `Fixpoint`) that takes two numbers n and m and returns the
sum of these two numbers. The implementation is defined recursively with pattern matching. You might
think of this definition as “unwrapping” each application of S from the first argument until we
reach its O. Then we start wrapping the second argument in the same number of Ss.

Now we’re ready to prove something! Let’s prove that `0 + n == n`:

```Rocq
Theorem plus_O_n :
  forall n : nat, plus O n = n.
Proof.
  intros n. simpl. reflexivity.
Qed.
```

We first define our theorem and give it a name (plus_O_n). Then we define the proof goal, in the
form of a dependent type. We claim that for all n, where n is an instance of our nat type, 0 + n is
equal to n. Finally, we construct a proof, in the form of a series of tactics. Tactics may implement
either backwards inference (transforming the goal) or forwards inference (transforming evidence).

The best way to understand the system is to run the software yourself, and play around with the
various tactics. In this case the goal is simple enough; once we’ve specified that the proof will be
on n, Rocq is able to simplify plus O n into n, leaving us the goal n = n. This turns out to be true
by the definition of equality, and we invoke definitional equality by reflexivity.

More complicated proofs do not typically require proving basic facts about arithmetic, because Rocq
ships a substantial standard library of useful definitions and theorems. The above example hopefully
serves to illustrate the formal nature of proof in these systems. In many cases it can be
surprisingly hard to convince the kernel of the correctness of a statement that seems “obviously”
true.

## Act Export

Calling `act rocq ...` will generate a Rocq file that encodes the contract as a state transition system,
following the formal value semantics, given in the
<span style="color:red">tech report (to be available shortly).</span>

The generated Rocq output will contain:
- Gallina type definitions for contract **state**.
- For every case of the constructor and every transition: 
  * **State transition function** (used for the step function).
  * **Precondition** and **postcondition** predicates (additionally to the given preconditions, also requirements on integer bounds)
  for every storage variable, where applicable. For transitions, postconditions need only hold for the reachable states (see below).
  * **Return value** proposition (only for transitions).
- **Transition system with a step function** (and then generalised to multistep)
- Definition of a **reachable state** *from a given state*.
- Definition of a **reachable state** *from the initial state*.
- Definition schema for the **invariants**: 
  * Parametrized by the invariant property `IP : Env -> Z -> State -> Prop`.
  * Invariant predicate definition for the Initial State.
  * Invariant predicate definition for the Step.
  * Proof of the invariant holding in all reachable states if `IP` holds in the initial state and for every step.

Let us explore the generated Rocq output for the ERC20 Token contract from [erc20.act](https://github.com/argotorg/act/blob/main/tests/hevm/pass/multisource/erc20/erc20.act).

The output will begin with importing the necessary libraries:
```Rocq
(* --- GENERATED BY ACT --- *)

Require Import Stdlib.ZArith.ZArith.
Require Import ActLib.ActLib.
Require Stdlib.Strings.String.

Module Str := Stdlib.Strings.String.
Open Scope Z_scope.
```

Then it will start a module for the token contract:

```Rocq
Module Token.

Record State : Set := state
{ addr : address
; allowance : address -> address -> Z
; balanceOf : address -> Z
; totalSupply : Z
}.
```
The contract will be represented as a record with the fields corresponding to the storage variables.
Note that we use the type `Z` for integers, which is the integer type from the ZArith library bundled with Rocq; 
and we also use the type `address` for Ethereum addresses, which is also represented by `Z` in the `ActLib`.

Next, the output contains some additional type definitions, like `noAliasing` and `integerBounds` (see `amm.act` contract for examples on how to use it - <span style="color:red">some of these may be outdated.</span>).
```Rocq
Inductive contractAddressIn : Z -> State -> Prop :=
| addressOf_This : forall (STATE : State),
     contractAddressIn (addr STATE) STATE
.

Inductive addressIn : Z -> State -> Prop :=
| address_addr : forall (STATE : State),
     addressIn (addr STATE) STATE

| address_subcontract : forall (p : address) (STATE : State),
     contractAddressIn p STATE -> addressIn p STATE
.

Inductive noAliasing (STATE : State) : Prop :=
| noAliasingC : noAliasing STATE
.

Inductive integerBounds (STATE : State) : Prop :=
| integerBoundsC :
     (forall i0 i1, 0 <= allowance STATE i0 i1 <= UINT_MAX 256)
  -> (forall i0, 0 <= balanceOf STATE i0 <= UINT_MAX 256)
  -> 0 <= totalSupply STATE <= UINT_MAX 256
  -> integerBounds STATE
.

Inductive integerBoundsRec (STATE : State) : Prop :=
| integerBoundsRecC :
     (forall i0 i1, 0 <= allowance STATE i0 i1 <= UINT_MAX 256)
  -> (forall i0, 0 <= balanceOf STATE i0 <= UINT_MAX 256)
  -> 0 <= totalSupply STATE <= UINT_MAX 256
  -> integerBoundsRec STATE
.

Definition nextAddrConstraint (ENV : Env) (STATE : State) :=
  forall (p : address), addressIn p STATE -> NextAddr ENV > p
.
```

Next, the `Token` constructor state transition of type `Env -> Z -> Env * State` is defined as follows: 

```Rocq
Definition Token (ENV : Env) (_totalSupply : Z) :=
  let ENV1 := NextEnv ENV in
  (ENV1, state (NextAddr ENV) 
               (fun _binding_0 _binding_1 => ((fun _ _ => 0) _binding_0 _binding_1)) 
               (fun _binding_0 => if ((_binding_0=?(Caller ENV)))%bool 
                                  then _totalSupply 
                                  else ((fun _ => 0) _binding_0)) 
                _totalSupply).
```
The constructor will take the environment and its input arguments, and produce a new environment and a new state for the token contract. The contract will be stored in the next address `NextAddr ENV`. The `allowance` function will be initialized to return 0 for all pairs of addresses, the `balanceOf` function will return the total supply for the contract creator, and the `totalSupply` will be set to the initial total supply.

Similarly, a state transition is generated for every case of every transition in the contract specification.

Next the preconditions for the constructor are generated as follows:
```
Inductive initPreconds (ENV : Env) (_totalSupply : Z) : Prop :=
| ctorPreconds :
     ((Callvalue ENV) = 0)
  -> ((0 <= _totalSupply) /\ (_totalSupply <= (UINT_MAX 256)))
  -> ((0 <= (Callvalue ENV)) /\ ((Callvalue ENV) <= (UINT_MAX 256)))
  -> ((0 <= (Caller ENV)) /\ ((Caller ENV) <= (UINT_MAX 160)))
  -> Caller ENV < NextAddr ENV
  -> Origin ENV < NextAddr ENV
  -> This ENV <> Caller ENV
  -> This ENV <> Origin ENV
  -> This ENV = NextAddr ENV
  -> initPreconds ENV _totalSupply.
```
The proposition holds, when the preconditions are satisfied: the integer bounds are respected, the
addresses are in range, and the environment is well-formed (for instance the next address is greater than all current addresses).

Similarly preconditions are generated for every case of every transition in the contract specification.



Note: reachability will also include steps for the contracts that are in the storage of your contract, see AMM for example.


<!-- The exponentiation contract -->
<!-- The following defines a contract that implements exponentiation via repeated
multiplication. The contract is initialized with a base (`b`) and an exponent (`e`). `exp()` can then be
repeatedly called until `e` is 1, and the result can then be read from the storage variable `r`. While
obviously artificial, this example does highlight a key shortcoming of the SMT based analysis:
exponentiation with a symbolic exponent is simply inexpressible in the smt-lib language used by all
major SMT solvers, and so any contract making use of exponentiation where the exponent is a variable
of some kind (e.g. calldata, storage) will be impossible to verify using SMT. Rocq has no such
restrictions, and we can export the spec below and prove correctness there.

```act
constructor of Exponent
interface constructor(uint _b, uint _e)

iff

    _e > 0

creates

    uint b := _b
    uint e := _e
    uint r := _b
```

```act
behaviour exp of Exponent
interface exp()

iff

    e > 1

iff in range uint

    r * b
    e - 1

storage

    r => r * b
    e => e - 1
    b
```

You can export the spec into Rocq by running `act Rocq --file Exponent.act`. This will create a file called Exponent.v which contains a model of the above Act specification in Rocq:

```Rocq
(* --- GENERATED BY ACT --- *)

Require Import Rocq.ZArith.ZArith.
Require Import ActLib.ActLib.
Require Rocq.Strings.String.

Module Str := Rocq.Strings.String.
Open Scope Z_scope.

Record State : Set := state
{ b : Z
; e : Z
; r : Z
}.

Definition exp0 (STATE : State)  :=
state (b STATE) (((e STATE) - 1)) (((r STATE) * (b STATE))).

Definition Exponent0 (_b : Z) (_e : Z) :=
state (_b) (_e) (_b).

Inductive reachable  : State -> State -> Prop :=
| Exponent0_base : forall (_b : Z) (_e : Z),
     (_e > 0)
  -> ((0 <= _b) /\ (_b <= (UINT_MAX 256)))
  -> ((0 <= _e) /\ (_e <= (UINT_MAX 256)))
  -> reachable (Exponent0 _b _e) (Exponent0 _b _e)

| exp0_step : forall (BASE STATE : State),
     reachable BASE STATE
  -> ((e STATE) > 1)
  -> ((0 <= ((r STATE) * (b STATE))) /\ (((r STATE) * (b STATE)) <= (UINT_MAX 256)))
  -> ((0 <= ((e STATE) - 1)) /\ (((e STATE) - 1) <= (UINT_MAX 256)))
  -> ((0 <= (r STATE)) /\ ((r STATE) <= (UINT_MAX 256)))
  -> ((0 <= (e STATE)) /\ ((e STATE) <= (UINT_MAX 256)))
  -> ((0 <= (b STATE)) /\ ((b STATE) <= (UINT_MAX 256)))
  -> reachable BASE (exp0 STATE )
.
```

Let’s break this down a bit. We have a definition of contract storage State, which consists of three
variables `b`, `e` and `r`, all of type `Z`. `Z` is an integer type using a binary encoding from the
ZArith library bundled with Rocq.

Next we have `exp0`, which defines how the state is updated by the exp behaviour, and `Exponent0` which
defines how the state variables are initialized by the constructor arguments.

Finally we have an Inductive Proposition reachable that defines the conditions under which a certain
state is reachable from another. There are two parts to this definition:

- `Exponent0_base`: states that given two integers `_b` and `_e`, the initial state is reachable
- from the initial state if `_e` and `_b` are in the range of a `uint256` and `_e` is greater than
- `0`. `exp0_step`: states that for a pair of states `BASE` and `STATE`, `exp0 STATE` (i.e. the
- result of calling `exp()` against an arbitrary contract state) is reachable from `BASE` if `STATE`
- is reachable from `BASE`, all the state variables in `STATE (e, b, r)` are within the range of a
- `uint256`, the result of the calculations `r * b` and `e - 1` are within the range of a `uint256`,
- and `e` is greater than 1.

This gives us a pair of inference rules that we can use to prove facts about the set of reachable
states defined by the specification for the Exponent contract.

The core fact that we wish to prove is that when `e` is 1, `r` is equal to `b ^ e`. This can be
expressed in Rocq as:

`forall (base, s : State), reachable base s -> e s = 1 -> r s = (b base) ^ (e base)`. Expressed more
verbosely: for all states `base` and `s`, if `s` is reachable from `base`, and the value of `e` in
`s` is 1, then the result variable `r` in `s` is equal to `b` from base raised to the power of `e`
from base.

The full proof is reproduced below. While an explanation of each step is out of scope for this post
(and is anyway best made with the proof loaded into an interactive instance of the Rocq prover like
proof general or RocqIde), we can give a broad strokes overview.

We must first define a helper fact `pow_pred` which simply states that given two integers `a` and
`e`, if e is greater than 0 then `a * a ^ (e - 1)` is equal to `a ^ e`. This fact is needed in the
later steps of the proof. The next step is to define a loop invariant for `exp()` (i.e. a fact that
is true before and after each loop iteration). This is the Lemma `invariant`, which states that for
every state `s` reachable from `base`, `r * b ^ (e - 1)` over `s` is equal to `b ^ e` over `base`.
Intuitively, this states that the partial result calculated so far (`r`), multiplied by the
remaining portion of the input calculation `b ^ (e - 1)` is equal to the final expected result.
Finally, given these two intermediate facts, we can discharge a proof for the correctness of
Exponent as defined above.

```Rocq
Require Import Exponent.Exponent.
Require Import ActLib.ActLib.
Require Import Rocq.ZArith.ZArith.
Open Scope Z_scope.

Lemma pow_pred : forall a e, 0 < e -> a * a ^ (Z.pred e) = a ^ e.
Proof.
  intros.
  apply eq_sym.
  replace (a ^ e) with (a ^ (Z.succ (Z.pred e))).
  - apply Z.pow_succ_r.
    apply Zlt_0_le_0_pred.
    assumption.
  - rewrite (Z.succ_pred e).
    reflexivity.
Qed.

Lemma invariant : forall base s,
  reachable base s -> (r s) * (b s) ^ ((e s) - 1) = (b base) ^ (e base).
Proof.
  intros base s H. induction H.
  - simpl.
    rewrite Z.sub_1_r.
    apply pow_pred.
    apply Z.gt_lt.
    assumption.
  - simpl.
    rewrite <- IHreachable.
    rewrite Z.sub_1_r.
    rewrite <- (pow_pred (b STATE) (e STATE - 1)).
    + rewrite Z.mul_assoc. reflexivity.
    + apply Z.gt_lt in H0.
      apply (proj1 (Z.sub_lt_mono_r 1 (e STATE) 1)).
      assumption.
Qed.

Theorem exp_correct : forall base s,
  reachable base s -> e s = 1 -> r s = (b base) ^ (e base).
Proof.
  intros base s H He.
  apply invariant in H.
  rewrite He in H. simpl in H.
  rewrite (Z.mul_1_r (r s)) in H.
  assumption.
Qed. Check exp_correct.
```

While this may seem like quite a lot of work to prove what looks like a pretty simple and obvious fact it is worth noting two things:

- A proof of this property is beyond the reach of any automated tool available today.
- Our mind is full of hidden assumptions, and facts that may seem obvious are not always so. This is not the case for the Rocq proof kernel, and once we have convinced it that something is true, we can be very sure that it really is. -->
