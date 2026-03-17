(** * Syntax
    Formalizes Section 1 of the tech report: types, expressions,
    references, slot expressions, mapping expressions, and top-level
    constructs (contracts, constructors, transitions). *)

From Stdlib Require Import String ZArith List Bool.
From Act Require Import Maps.
Import ListNotations.

(* ================================================================= *)
(** ** Types *)

(** Integer bit-width: M ∈ {8,16,...,256}.
    We keep it abstract as a [nat] (the actual value 8*i). *)
Definition bitwidth := nat.

(** Integer types ι *)
Inductive int_type : Type :=
  | UintT : bitwidth -> int_type   (** uint M *)
  | IntT  : bitwidth -> int_type   (** int M  *)
  | IntUnbounded : int_type.       (** int (unbounded, mathematical) *)

(** Base types β *)
Inductive base_type : Type :=
  | TInt     : int_type -> base_type
  | TBool    : base_type
  | TAddress : base_type.

(** Mapping types μ *)
Inductive mapping_type : Type :=
  | MBase : base_type -> mapping_type
  | MMapping : base_type -> mapping_type -> mapping_type.

(** ABI types α — base types plus typed contract addresses *)
Inductive abi_type : Type :=
  | ABase : base_type -> abi_type
  | AContractAddr : ident -> abi_type.  (** address_Id *)

(** Slot types σ — the type of storage slots *)
Inductive slot_type : Type :=
  | SMapping : mapping_type -> slot_type
  | SAbi     : abi_type -> slot_type
  | SContract : ident -> slot_type.

(** Optional slot type (⊥ or σ), used when Id may be absent *)
Inductive opt_id : Type :=
  | ONone : opt_id           (** ⊥ *)
  | OSome : ident -> opt_id. (** Id *)

(* ================================================================= *)
(** ** Binary Operators *)

Inductive int_binop : Type :=
  | OpAdd | OpSub | OpMul | OpDiv | OpMod | OpExp.

Inductive bool_binop : Type :=
  | OpAnd | OpOr | OpImpl.

Inductive cmp_op : Type :=
  | CmpLt | CmpLe | CmpGe | CmpGt.

(* ================================================================= *)
(** ** Environment Variables *)

Inductive env_var : Type :=
  | EnvCaller | EnvOrigin | EnvCallvalue | EnvThis.

(* ================================================================= *)
(** ** Variable References *)

Inductive ref : Type :=
  | RVar      : ident -> ref                (** x *)
  | RPre      : ident -> ref                (** pre(x) *)
  | RPost     : ident -> ref                (** post(x) *)
  | RCoerce   : ref -> ident -> ref         (** ref as Id *)
  | RField    : ref -> ident -> ref         (** ref.y *)
  | RIndex    : ref -> expr -> ref          (** ref[e] *)
  | REnv      : env_var -> ref              (** env *)

(* ================================================================= *)
(** ** Base Expressions *)

with expr : Type :=
  | EInt      : Z -> expr                           (** integer literal *)
  | EBool     : bool -> expr                        (** boolean literal *)
  | ERef      : ref -> expr                         (** ref (with type annotation erased) *)
  | EAddr     : ref -> expr                         (** addr(ref) *)
  | EBopI     : expr -> int_binop -> expr -> expr   (** e ○_i e *)
  | EBopB     : expr -> bool_binop -> expr -> expr  (** e ○_b e *)
  | ECmp      : expr -> cmp_op -> expr -> expr      (** e ⋈ e *)
  | ENeg      : expr -> expr                        (** ¬ e *)
  | EInRange  : int_type -> expr -> expr            (** inrange(ι, e) *)
  | EITE      : expr -> expr -> expr -> expr        (** if e then e else e *)
  | EEq       : expr -> expr -> expr.               (** e = e *)

(* ================================================================= *)
(** ** Mapping Expressions *)

Inductive map_expr : Type :=
  | MExp      : expr -> map_expr                                (** e *)
  | MMap      : list (expr * map_expr) -> mapping_type -> map_expr
      (** [e₁ => m₁, ...]_{mapping(β,μ)} *)
  | MMapUpd   : ref -> list (expr * map_expr) -> mapping_type -> map_expr.
      (** ref [e₁ => m₁, ...]_{mapping(β,μ)} *)

(* ================================================================= *)
(** ** Slot Expressions *)

Inductive slot_expr : Type :=
  | SEMap     : map_expr -> slot_expr               (** m *)
  | SENew     : ident -> option slot_expr -> list slot_expr -> slot_expr
      (** new Id {value: se}?(se₁,...,seₙ) *)
  | SERef     : ref -> slot_expr                    (** ref *)
  | SEAddr    : slot_expr -> slot_expr.             (** addr(se) *)

(* ================================================================= *)
(** ** Creates, Updates *)

(** A single create: σ x := se *)
Definition create := (slot_type * ident * slot_expr)%type.

(** A single update: ref := se *)
Definition update := (ref * slot_expr)%type.

(* ================================================================= *)
(** ** Constructor and Transition Cases *)

(** Constructor case: case e: creates [...] *)
Definition ctor_case := (expr * list create)%type.

(** Transition case: case e: updates [...] returns e *)
Definition trans_case := (expr * list update * expr)%type.

(* ================================================================= *)
(** ** Constructors and Transitions *)

(** Interface: list of (variable name, abi type) pairs *)
Definition interface := list (ident * abi_type).

(** Constructor *)
Record constructor := mk_ctor {
  ctor_iface   : interface;
  ctor_payable : bool;
  ctor_iff     : list expr;         (** preconditions *)
  ctor_cases   : list ctor_case;    (** case blocks *)
  ctor_post    : list expr;         (** postconditions *)
}.

(** Transition *)
Record transition := mk_trans {
  trans_name    : ident;
  trans_iface   : interface;
  trans_payable : bool;
  trans_rettype : option abi_type;
  trans_iff     : list expr;        (** preconditions *)
  trans_cases   : list trans_case;  (** case blocks *)
  trans_post    : list expr;        (** postconditions *)
}.

(** Invariants *)
Definition invariants := list expr.

(** Contract *)
Record contract := mk_contract {
  contract_name   : ident;
  contract_ctor   : constructor;
  contract_trans  : list transition;
  contract_inv    : invariants;
}.

(** Specification: a list of contracts *)
Definition spec := list contract.

(* ================================================================= *)
(** ** Contract Storage *)

(** Contract storage type C: maps variable names to slot types *)
Definition storage_layout := list (ident * slot_type).

(* ================================================================= *)
(** ** More-specific relation on references (Section 5) *)

(** ref₁ ≺_specific ref₂ *)
Inductive more_specific : ref -> ref -> Prop :=
  | MS_field : forall r x,
      more_specific (RField r x) r
  | MS_trans : forall r1 r2 x,
      more_specific r1 r2 ->
      more_specific (RField r1 x) r2.

(** ref₁ ⪯_specific ref₂ (reflexive closure) *)
Definition more_specific_eq (r1 r2 : ref) : Prop :=
  r1 = r2 \/ more_specific r1 r2.
