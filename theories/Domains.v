(** * Semantic Domains
    Values, states, and environments for the pointer semantics
    (Section 2 of the tech report). *)

From Stdlib Require Import String ZArith List Bool PeanoNat Lia.
From Act Require Import Maps Syntax.
Import ListNotations.

(* ================================================================= *)
(** ** Addresses *)

Definition addr := nat.

(* ================================================================= *)
(** ** Values *)

(** BaseValue ≡ Z + B + Addr *)
Inductive base_value : Type :=
  | BVInt  : Z -> base_value
  | BVBool : bool -> base_value
  | BVAddr : addr -> base_value.

(** Value ≡ (Z → Value) + (B → Value) + (Addr → Value) + BaseValue *)
Inductive value : Type :=
  | VBase  : base_value -> value
  | VMapZ  : (Z -> value) -> value
  | VMapB  : (bool -> value) -> value
  | VMapA  : (addr -> value) -> value.

(** Coercions from base values *)
Definition VInt (n : Z) : value := VBase (BVInt n).
Definition VBool (b : bool) : value := VBase (BVBool b).
Definition VAddr (a : addr) : value := VBase (BVAddr a).

(* ================================================================= *)
(** ** State *)

(** A single storage location stores a contract type name and
    a mapping from variable names to values. *)
Record loc_store := mk_loc_store {
  loc_type : ident;
  loc_vars : partial_map value;
}.

(** State: a store mapping addresses to location stores,
    together with the next fresh address and a proof that it is fresh. *)
Record state := mk_state {
  state_store :> addr -> option loc_store;
  state_next : addr;
  state_fresh : forall l, l >= state_next -> state_store l = None;
}.

Definition state_empty : state :=
  mk_state (fun _ => None) 0 (fun _ _ => eq_refl).

Definition state_lookup (s : state) (l : addr) : option loc_store := s l.

Definition state_dom (s : state) (l : addr) : Prop :=
  exists ls, s l = Some ls.

(** If a location is in the domain, its address is below state_next. *)
Lemma state_store_bound : forall (s : state) (l : addr) (ls : loc_store),
  s l = Some ls -> l < state_next s.
Proof.
  intros s l ls H.
  destruct (Nat.lt_ge_cases l (state_next s)) as [Hlt | Hge]; auto.
  rewrite (state_fresh s l Hge) in H. discriminate.
Qed.

Lemma state_dom_bound : forall s l, state_dom s l -> l < state_next s.
Proof. intros s l [ls H]. eapply state_store_bound; eauto. Qed.

Definition state_update (s : state) (l : addr) (ls : loc_store)
    (Hl : l < state_next s) : state :=
  mk_state
    (fun l' => if Nat.eqb l l' then Some ls else s l')
    (state_next s)
    (fun l' Hge =>
       match Nat.eqb_spec l l' with
       | ReflectT _ Heq =>
           ltac:(exfalso; abstract lia)
       | ReflectF _ _ => state_fresh s l' Hge
       end).

(** s(ℓ).type *)
Definition state_type (s : state) (l : addr) : option ident :=
  match s l with
  | Some ls => Some (loc_type ls)
  | None => None
  end.

(** s(ℓ)(x) *)
Definition state_var (s : state) (l : addr) (x : ident) : option value :=
  match s l with
  | Some ls => loc_vars ls x
  | None => None
  end.

(** x ∈ dom(s(ℓ)) *)
Definition state_var_dom (s : state) (l : addr) (x : ident) : Prop :=
  exists v, state_var s l x = Some v.

(** Force-extract a value from state, defaulting to VInt 0 *)
Definition state_var_force (s : state) (l : addr) (x : ident) : value :=
  match state_var s l x with
  | Some v => v
  | None => VInt 0%Z
  end.

(** Update a single variable in the store at location ℓ:
    s[ℓ ↦ s(ℓ)[x ↦ v]] *)
Definition state_update_var (s : state) (l : addr) (x : ident) (v : value) : state :=
  mk_state
    (fun l' => match s l with
               | Some ls =>
                   if Nat.eqb l l' then
                     Some (mk_loc_store (loc_type ls) (Maps.update (loc_vars ls) x v))
                   else s l'
               | None => s l'
               end)
    (state_next s)
    ltac:(intros l' Hge; destruct (s l) eqn:El;
          [ destruct (Nat.eqb_spec l l');
            [exfalso; apply (state_store_bound s l) in El; lia
            |apply state_fresh; lia]
          | apply state_fresh; lia]).

(** Spec lemmas for state_update and state_update_var *)
Lemma state_update_store : forall s l ls Hl l',
  state_update s l ls Hl l' = if Nat.eqb l l' then Some ls else s l'.
Proof. reflexivity. Qed.

Lemma state_update_next_eq : forall s l ls Hl,
  state_next (state_update s l ls Hl) = state_next s.
Proof. reflexivity. Qed.

Lemma state_update_var_store : forall s l x v l',
  state_update_var s l x v l' =
  match s l with
  | Some ls => if Nat.eqb l l' then
      Some (mk_loc_store (loc_type ls) (Maps.update (loc_vars ls) x v))
      else s l'
  | None => s l'
  end.
Proof. reflexivity. Qed.

Lemma state_update_var_next : forall s l x v,
  state_next (state_update_var s l x v) = state_next s.
Proof. reflexivity. Qed.

(** Allocate a new location using the next fresh address. *)
Definition state_alloc (s : state) (id : ident) (bindings : partial_map value) : state :=
  let l := state_next s in
  mk_state
    (fun l' => if Nat.eqb l l' then Some (mk_loc_store id bindings) else s l')
    (S l)
    (fun l' Hge =>
       match Nat.eqb_spec l l' with
       | ReflectT _ Heq =>
           ltac:(exfalso; abstract lia)
       | ReflectF _ _ =>
           state_fresh s l' ltac:(abstract lia)
       end).

Definition state_alloc_addr (s : state) : addr := state_next s.

Lemma state_alloc_store : forall s id bindings l',
  state_alloc s id bindings l' =
  if Nat.eqb (state_next s) l' then Some (mk_loc_store id bindings) else s l'.
Proof. reflexivity. Qed.

Lemma state_alloc_next : forall s id bindings,
  state_next (state_alloc s id bindings) = S (state_next s).
Proof. reflexivity. Qed.

Lemma state_alloc_self : forall s id bindings,
  state_alloc s id bindings (state_next s) = Some (mk_loc_store id bindings).
Proof. intros. rewrite state_alloc_store. rewrite Nat.eqb_refl. auto. Qed.

Lemma state_alloc_other : forall s id bindings l',
  l' <> state_next s ->
  state_alloc s id bindings l' = s l'.
Proof.
  intros. rewrite state_alloc_store.
  destruct (Nat.eqb_spec (state_next s) l'); auto. subst. exfalso; auto.
Qed.

(** State inclusion: s ⊆ s' means dom(s) ⊆ dom(s') and
    for all ℓ ∈ dom(s), s(ℓ) = s'(ℓ). *)
Definition state_incl (s s' : state) : Prop :=
  forall l ls, s l = Some ls -> s' l = Some ls.

Lemma state_incl_alloc : forall s id bindings,
  state_incl s (state_alloc s id bindings).
Proof.
  intros s id bindings l ls H.
  rewrite state_alloc_other; auto.
  intro Heq. subst. pose proof (state_store_bound _ _ _ H). lia.
Qed.

(* ================================================================= *)
(** ** Environment *)

(** Env ≡ String ⇀ BaseValue
    For our formalization, the environment maps identifiers to values
    (since base values are embedded in values). *)
Definition env := partial_map value.

(* ================================================================= *)
(** ** Timing Tags *)

(** The tag t on references: U (untimed) or T (timed) *)
Inductive time_tag : Type :=
  | TagU : time_tag    (** untimed *)
  | TagT : time_tag.   (** timed *)

(** The timing of an evaluated reference: U, pre, or post *)
Inductive ref_time : Type :=
  | RTU    : ref_time   (** untimed *)
  | RTPre  : ref_time   (** pre-state *)
  | RTPost : ref_time.  (** post-state *)

(** Timed state: either a single state (untimed) or a pair (timed) *)
Inductive timed_state : Type :=
  | TSUntimed : state -> timed_state
  | TSTimed   : state -> state -> timed_state. (** (s_pre, s_post) *)

(* ================================================================= *)
(** ** State Environment Σ *)

(** The typing environment Σ has three components:
    - Storage: maps contract names to their storage layout
    - Cnstr: maps contract names to their constructor
    - Trans: maps contract names to their list of transitions
    We use association lists for finite enumerability (needed for
    induction on Σ-size in type safety proofs). *)
Record contract_env := mk_contract_env {
  Σ_storage_list : alist storage_layout;
  Σ_cnstr_list   : alist constructor;
  Σ_trans_list   : alist (list transition);
}.

(** Accessor functions (partial_map view) *)
Definition Σ_storage (Σ : contract_env) : partial_map storage_layout :=
  alist_lookup (Σ_storage_list Σ).
Definition Σ_cnstr (Σ : contract_env) : partial_map constructor :=
  alist_lookup (Σ_cnstr_list Σ).
Definition Σ_trans (Σ : contract_env) : partial_map (list transition) :=
  alist_lookup (Σ_trans_list Σ).

Definition Σ_empty : contract_env := mk_contract_env [] [] [].

(** Σ with updated storage *)
Definition Σ_with_storage (Σ : contract_env) (id : ident) (c : storage_layout) : contract_env :=
  mk_contract_env ((id, c) :: Σ_storage_list Σ) (Σ_cnstr_list Σ) (Σ_trans_list Σ).

(** Σ with updated constructor *)
Definition Σ_with_cnstr (Σ : contract_env) (id : ident) (ct : constructor) : contract_env :=
  mk_contract_env (Σ_storage_list Σ) ((id, ct) :: Σ_cnstr_list Σ) (Σ_trans_list Σ).

(** Σ with updated transitions *)
Definition Σ_with_trans (Σ : contract_env) (id : ident) (ts : list transition) : contract_env :=
  mk_contract_env (Σ_storage_list Σ) (Σ_cnstr_list Σ) ((id, ts) :: Σ_trans_list Σ).

(** Size of Σ (number of constructor entries) *)
Definition Σ_cnstr_size (Σ : contract_env) : nat := length (Σ_cnstr_list Σ).

(** Interaction lemmas: Σ_with_* and accessors *)
Lemma Σ_storage_with_storage : forall Σ id c,
  Σ_storage (Σ_with_storage Σ id c) = Maps.update (Σ_storage Σ) id c.
Proof. reflexivity. Qed.
Lemma Σ_cnstr_with_storage : forall Σ id c,
  Σ_cnstr (Σ_with_storage Σ id c) = Σ_cnstr Σ.
Proof. reflexivity. Qed.
Lemma Σ_trans_with_storage : forall Σ id c,
  Σ_trans (Σ_with_storage Σ id c) = Σ_trans Σ.
Proof. reflexivity. Qed.

Lemma Σ_storage_with_cnstr : forall Σ id ct,
  Σ_storage (Σ_with_cnstr Σ id ct) = Σ_storage Σ.
Proof. reflexivity. Qed.
Lemma Σ_cnstr_with_cnstr : forall Σ id ct,
  Σ_cnstr (Σ_with_cnstr Σ id ct) = Maps.update (Σ_cnstr Σ) id ct.
Proof. reflexivity. Qed.
Lemma Σ_trans_with_cnstr : forall Σ id ct,
  Σ_trans (Σ_with_cnstr Σ id ct) = Σ_trans Σ.
Proof. reflexivity. Qed.

Lemma Σ_storage_with_trans : forall Σ id ts,
  Σ_storage (Σ_with_trans Σ id ts) = Σ_storage Σ.
Proof. reflexivity. Qed.
Lemma Σ_cnstr_with_trans : forall Σ id ts,
  Σ_cnstr (Σ_with_trans Σ id ts) = Σ_cnstr Σ.
Proof. reflexivity. Qed.
Lemma Σ_trans_with_trans : forall Σ id ts,
  Σ_trans (Σ_with_trans Σ id ts) = Maps.update (Σ_trans Σ) id ts.
Proof. reflexivity. Qed.

Lemma Σ_cnstr_size_with_cnstr : forall Σ id ct,
  Σ_cnstr_size (Σ_with_cnstr Σ id ct) = S (Σ_cnstr_size Σ).
Proof. reflexivity. Qed.

Lemma Σ_cnstr_size_with_storage : forall Σ id c,
  Σ_cnstr_size (Σ_with_storage Σ id c) = Σ_cnstr_size Σ.
Proof. reflexivity. Qed.

Lemma Σ_cnstr_size_with_trans : forall Σ id ts,
  Σ_cnstr_size (Σ_with_trans Σ id ts) = Σ_cnstr_size Σ.
Proof. reflexivity. Qed.

(** Σ ⊆ Σ' *)
Definition Σ_incl (Σ Σ' : contract_env) : Prop :=
  includes (Σ_storage Σ) (Σ_storage Σ') /\
  includes (Σ_cnstr Σ) (Σ_cnstr Σ') /\
  includes (Σ_trans Σ) (Σ_trans Σ').

(** Look up a storage variable type: Σ_Storage(A)(x) *)
Definition Σ_storage_var (Σ : contract_env) (a : ident) (x : ident) : option slot_type :=
  match Σ_storage Σ a with
  | Some layout => alist_lookup layout x
  | None => None
  end.

(** Σ ⊢ ℓ :_s A — shorthand for: location ℓ has contract type A in state s *)
(** (defined formally in ValueTyping.v) *)

(** Helper: is a constructor payable? *)
Definition isPayable (ct : constructor) : bool := ctor_payable ct.

(** dummy location — used when location is irrelevant (written · in the paper) *)
Definition dummy_loc : addr := 0.

(** meta(β) — the Coq type corresponding to a base type *)
(** meta(ι) = Z, meta(bool) = B, meta(address) = Addr *)
(** We don't reify this as a Coq type; instead we use predicates on values. *)

(** default(μ) — the default value of a mapping type *)
Fixpoint default_value (mu : mapping_type) : value :=
  match mu with
  | MBase (TInt _) => VInt 0%Z
  | MBase TBool => VBool false
  | MBase TAddress => VAddr 0
  | MMapping (TInt _) mu' => VMapZ (fun _ => default_value mu')
  | MMapping TBool mu' => VMapB (fun _ => default_value mu')
  | MMapping TAddress mu' => VMapA (fun _ => default_value mu')
  end.

(** min and max for integer types *)
Definition int_min (it : int_type) : option Z :=
  match it with
  | UintT _ => Some 0%Z
  | IntT m => Some (- Z.pow 2 (Z.of_nat m - 1))%Z
  | IntUnbounded => None  (** unbounded int has no min *)
  end.

Definition int_max (it : int_type) : option Z :=
  match it with
  | UintT m => Some (Z.pow 2 (Z.of_nat m) - 1)%Z
  | IntT m => Some (Z.pow 2 (Z.of_nat m - 1) - 1)%Z
  | IntUnbounded => None
  end.

(** In-range check: (min(ι) ≤ v ≤ max(ι)) ∨ ι = int *)
Definition in_range (it : int_type) (v : Z) : Prop :=
  match it with
  | IntUnbounded => True
  | _ =>
    match int_min it, int_max it with
    | Some lo, Some hi => (lo <= v)%Z /\ (v <= hi)%Z
    | _, _ => False
    end
  end.
