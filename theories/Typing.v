(** * Typing Judgments
    Formalizes Section 4 of the tech report: type well-formedness,
    reference judgments, expression judgments, mapping expression
    judgments, slot expression judgments, create/update judgments,
    constructor/transition judgments, and spec/contract judgments. *)

From Stdlib Require Import String ZArith List Bool PeanoNat Lia.
From Act Require Import Maps Syntax Domains Semantics ValueTyping.
Import ListNotations.

(** Correspondence with technical report.

    The Rocq development is the source of truth for the mechanized type system
    of Act. Its structure follows the tech report, but it intentionally fixes
    several stale points in the report:

    - Reference judgments carry an explicit path condition [phi], that is used
      to typecheck expressions used as mapping indices. This is missing from the
      tech report.

    - Integer arithmetic produces [IntUnbounded].  Narrowing to a bounded
      integer type is handled by [T_NumConv], and only for untimed expressions,
      with a [semantic_entailment] proof that the runtime value lies in range.
      This differs from the older report presentation where [T_BopI] could
      directly synthesize a bounded integer result.

    - Constructor and transition case consistency follows the report's
      semantic-entailment check.  Rocq encodes the report's coverage plus
      pairwise-exclusion formula as the recursive boolean expression
      [exactly_one_expr], with preconditions carried in [phi].  The proof then
      derives the evaluator-facing active case from that entailment.

    - Update non-overlap is checked only against earlier updates ([j < i]). The
      report's inclusive interval is a typo: including [j = i] would make every
      update overlap with itself. *)

(* ================================================================= *)
(** ** S/N tags for reference judgment *)

Inductive ref_tag : Type :=
  | TagS : ref_tag   (** storage reference reachable without coercion *)
  | TagN : ref_tag.  (** calldata, coerced, or environment reference *)

(* ================================================================= *)
(** ** Type Well-formedness *)

Definition valid_bitwidth (m : bitwidth) : Prop :=
  (8 <= m <= 256)%nat /\ Nat.modulo m 8 = 0.

Definition base_type_wf (bt : base_type) : Prop :=
  match bt with
  | TInt (UintT m) => valid_bitwidth m
  | TInt (IntT m) => valid_bitwidth m
  | TInt IntUnbounded => False
  | TBool => True
  | TAddress => True
  end.

Fixpoint mapping_type_wf (mu : mapping_type) : Prop :=
  match mu with
  | MBase bt => base_type_wf bt
  | MMapping bt mu' => base_type_wf bt /\ mapping_type_wf mu'
  end.

(** Σ ⊢ α wf *)
Inductive abi_type_wf (Σ : contract_env) : abi_type -> Prop :=
  | WF_Int : forall it,
      base_type_wf (TInt it) ->
      abi_type_wf Σ (ABase (TInt it))
  | WF_Bool :
      abi_type_wf Σ (ABase TBool)
  | WF_Address :
      abi_type_wf Σ (ABase TAddress)
  | WF_ContractAddr : forall a,
      dom (Σ_storage Σ) a ->
      abi_type_wf Σ (AContractAddr a).

(** Σ ⊢ σ wf *)
Inductive slot_type_wf (Σ : contract_env) : slot_type -> Prop :=
  | WF_Contract : forall a,
      dom (Σ_storage Σ) a ->
      slot_type_wf Σ (SContract a)
  | WF_SAbi : forall alpha,
      abi_type_wf Σ alpha ->
      slot_type_wf Σ (SAbi alpha)
  | WF_SMapping : forall mu,
      mapping_type_wf mu ->
      slot_type_wf Σ (SMapping mu).

Lemma valid_bitwidth_zero_in_range_uint :
  forall m, valid_bitwidth m -> in_range (UintT m) 0%Z.
Proof.
  intros m Hwf. simpl. split; [lia|].
  assert (Hpow : (0 < 2 ^ Z.of_nat m)%Z).
  { apply Z.pow_pos_nonneg; lia. }
  lia.
Qed.

Lemma valid_bitwidth_zero_in_range_int :
  forall m, valid_bitwidth m -> in_range (IntT m) 0%Z.
Proof.
  intros m Hwf. simpl. destruct Hwf as [[Hlo Hhi] Hmod].
  assert (Hexp : (0 <= Z.of_nat m - 1)%Z) by lia.
  split.
  - assert (Hpow : (0 < 2 ^ (Z.of_nat m - 1))%Z).
    { apply Z.pow_pos_nonneg; lia. }
    lia.
  - assert (Hpow : (0 < 2 ^ (Z.of_nat m - 1))%Z).
    { apply Z.pow_pos_nonneg; lia. }
    lia.
Qed.

Lemma base_int_zero_in_range :
  forall it, base_type_wf (TInt it) -> in_range it 0%Z.
Proof.
  intros [m|m|] Hwf; simpl in Hwf; try contradiction.
  - apply valid_bitwidth_zero_in_range_uint. exact Hwf.
  - apply valid_bitwidth_zero_in_range_int. exact Hwf.
Qed.

Lemma default_has_mapping_type :
  forall mu, mapping_type_wf mu -> has_mapping_type (default_value mu) mu.
Proof.
  induction mu as [bt | bt mu IH]; simpl; intros Hwf.
  - constructor. destruct bt as [it| |]; constructor.
    apply base_int_zero_in_range. exact Hwf.
  - destruct Hwf as [_ Hmu].
    destruct bt as [it| |]; simpl; constructor; intros; apply IH; exact Hmu.
Qed.

(** Σ ⊢ I wf *)
Definition interface_wf (Σ : contract_env) (iface : interface) : Prop :=
  Forall (fun p => abi_type_wf Σ (snd p)) iface /\
  ~ alist_dom iface "caller"%string /\
  ~ alist_dom iface "origin"%string /\
  ~ alist_dom iface "callvalue"%string.

(* ================================================================= *)
(** ** Environment References Judgment *)
(** Σ; I ⊢_{⊥?Id} env : α *)

Inductive type_env_ref : contract_env -> interface -> opt_id -> env_var -> abi_type -> Prop :=
  | T_Caller : forall Σ iface oid,
      type_env_ref Σ iface oid EnvCaller (ABase TAddress)
  | T_Origin : forall Σ iface oid,
      type_env_ref Σ iface oid EnvOrigin (ABase TAddress)
  | T_Callvalue : forall Σ iface oid,
      type_env_ref Σ iface oid EnvCallvalue (ABase (TInt (UintT 256)))
  | T_This : forall Σ iface a,
      type_env_ref Σ iface (OSome a) EnvThis (AContractAddr a).

(* ================================================================= *)
(** ** Typing Assumptions *)

(** The report writes [true] for an empty path condition. In Rocq, a path
    condition is a list of boolean expressions that must all evaluate to true. *)
Definition empty_phi : list expr := [].

(** Branch-local assumptions: the selected case condition plus the surrounding
    constructor/transition preconditions. *)
Definition case_phi (pres : list expr) (cond : expr) : list expr :=
  cond :: pres.

(** Boolean expression saying that every expression in [es] evaluates to false. *)
Fixpoint all_false_expr (es : list expr) : expr :=
  match es with
  | [] => EBool true
  | e :: es' => EBopB (ENeg e) OpAnd (all_false_expr es')
  end.

(** Boolean expression saying that exactly one expression in [es] evaluates to
    true.  This is equivalent to the report's coverage plus pairwise-exclusion
    constraint, but it is structurally easier to use in Rocq proofs. *)
Fixpoint exactly_one_expr (es : list expr) : expr :=
  match es with
  | [] => EBool false
  | e :: es' =>
      EBopB
        (EBopB e OpAnd (all_false_expr es'))
        OpOr
        (EBopB (ENeg e) OpAnd (exactly_one_expr es'))
  end.

Definition ctor_case_conditions (cases : list ctor_case) : list expr :=
  map fst cases.

Definition trans_case_conditions (cases : list trans_case) : list expr :=
  map tc_cond cases.

Definition case_consistency_exprs (es : list expr) : list expr :=
  [exactly_one_expr es].

(** Non-payable constructor calls use an implicit zero callvalue. *)
Definition zero_callvalue_slot_expr : slot_expr := SEMap (MExp (EInt 0%Z)).

(* ================================================================= *)
(** ** Reference Judgment *)
(** Σ; I; Φ ⊢^k_{⊥?Id, t} ref : σ *)

Inductive type_ref : contract_env -> interface -> list expr ->
                      ref_tag -> opt_id -> time_tag ->
                      ref -> slot_type -> Prop :=
  (** T-Calldata *)
  | T_Calldata : forall Σ iface phi oid t x alpha,
      alist_lookup iface x = Some alpha ->
      type_ref Σ iface phi TagN oid t (RVar x) (SAbi alpha)

  (** T-Storage *)
  | T_Storage : forall Σ iface phi a x sty layout,
      Σ_storage Σ a = Some layout ->
      alist_lookup layout x = Some sty ->
      ~ alist_dom iface x ->
      x <> "caller"%string -> x <> "origin"%string -> x <> "callvalue"%string ->
      type_ref Σ iface phi TagS (OSome a) TagU (RVar x) sty

  (** T-StoragePre *)
  | T_StoragePre : forall Σ iface phi a x sty layout,
      Σ_storage Σ a = Some layout ->
      alist_lookup layout x = Some sty ->
      ~ alist_dom iface x ->
      x <> "caller"%string -> x <> "origin"%string -> x <> "callvalue"%string ->
      type_ref Σ iface phi TagS (OSome a) TagT (RPre x) sty

  (** T-StoragePost *)
  | T_StoragePost : forall Σ iface phi a x sty layout,
      Σ_storage Σ a = Some layout ->
      alist_lookup layout x = Some sty ->
      ~ alist_dom iface x ->
      x <> "caller"%string -> x <> "origin"%string -> x <> "callvalue"%string ->
      type_ref Σ iface phi TagS (OSome a) TagT (RPost x) sty

  (** T-Coerce *)
  | T_Coerce : forall Σ iface phi k oid t r a,
      type_ref Σ iface phi k oid t r (SAbi (AContractAddr a)) ->
      type_ref Σ iface phi TagN oid t (RCoerce r a) (SContract a)

  (** T-Upcast *)
  | T_Upcast : forall Σ iface phi k oid t r a,
      type_ref Σ iface phi k oid t r (SAbi (AContractAddr a)) ->
      type_ref Σ iface phi TagN oid t r (SAbi (ABase TAddress))

  (** T-Field *)
  | T_Field : forall Σ iface phi k oid t r a x sty,
      type_ref Σ iface phi k oid t r (SContract a) ->
      Σ_storage_var Σ a x = Some sty ->
      type_ref Σ iface phi k oid t (RField r x) sty

  (** T-MapIndex *)
  | T_MapIndex : forall Σ iface phi k oid t r e bt mu,
      type_ref Σ iface phi k oid t r (SMapping (MMapping bt mu)) ->
      type_expr Σ iface phi oid t e bt ->
      type_ref Σ iface phi TagN oid t (RIndex r e) (SMapping mu)

  (** T-Environment *)
  | T_Environment : forall Σ iface phi oid ev alpha,
      type_env_ref Σ iface oid ev alpha ->
      type_ref Σ iface phi TagN oid TagU (REnv ev) (SAbi alpha)

(* ================================================================= *)
(** ** Expression Judgment *)
(** Σ; I; Φ ⊢_{⊥?Id, t} e : β *)

with type_expr : contract_env -> interface -> list expr -> opt_id -> time_tag ->
                  expr -> base_type -> Prop :=
  (** T-Int *)
  | T_Int : forall Σ iface phi oid t n it,
      in_range it n ->
      type_expr Σ iface phi oid t (EInt n) (TInt it)

  (** T-Bool *)
  | T_Bool : forall Σ iface phi oid t b,
      type_expr Σ iface phi oid t (EBool b) TBool

  (** T-Ref *)
  | T_Ref : forall Σ iface phi oid t k r bt,
      type_ref Σ iface phi k oid t r (SAbi (ABase bt)) ->
      type_expr Σ iface phi oid t (ERef r) bt

  (** T-Addr *)
  | T_Addr : forall Σ iface phi oid k r a,
      type_ref Σ iface phi k oid TagU r (SContract a) ->
      type_expr Σ iface phi oid TagU (EAddr r) TAddress

  (** T-Range *)
  | T_Range : forall Σ iface phi oid t e it1 it2,
      type_expr Σ iface phi oid t e (TInt it2) ->
      type_expr Σ iface phi oid t (EInRange it1 e) TBool

  (** T-BopI *)
  | T_BopI : forall Σ iface phi oid t e1 op e2 it1 it2,
      type_expr Σ iface phi oid t e1 (TInt it1) ->
      type_expr Σ iface phi oid t e2 (TInt it2) ->
      type_expr Σ iface phi oid t (EBopI e1 op e2) (TInt IntUnbounded)

  (** T-NumConv: widening to mathematical integers is always allowed; narrowing
      to a bounded integer type requires a semantic range entailment. *)
  | T_NumConv : forall Σ iface phi oid t e it1 it2,
      type_expr Σ iface phi oid t e (TInt it1) ->
      (it2 = IntUnbounded \/
       (t = TagU /\ semantic_entailment Σ iface phi oid [EInRange it2 e])) ->
      type_expr Σ iface phi oid t e (TInt it2)

  (** T-BopB *)
  | T_BopB : forall Σ iface phi oid t e1 op e2,
      type_expr Σ iface phi oid t e1 TBool ->
      type_expr Σ iface phi oid t e2 TBool ->
      type_expr Σ iface phi oid t (EBopB e1 op e2) TBool

  (** T-Neg *)
  | T_Neg : forall Σ iface phi oid t e,
      type_expr Σ iface phi oid t e TBool ->
      type_expr Σ iface phi oid t (ENeg e) TBool

  (** T-Cmp *)
  | T_Cmp : forall Σ iface phi oid t e1 op e2 it,
      type_expr Σ iface phi oid t e1 (TInt it) ->
      type_expr Σ iface phi oid t e2 (TInt it) ->
      type_expr Σ iface phi oid t (ECmp e1 op e2) TBool

  (** T-ITE *)
  | T_ITE : forall Σ iface phi oid t e1 e2 e3 bt,
      type_expr Σ iface phi oid t e1 TBool ->
      type_expr Σ iface phi oid t e2 bt ->
      type_expr Σ iface phi oid t e3 bt ->
      type_expr Σ iface phi oid t (EITE e1 e2 e3) bt

  (** T-Eq *)
  | T_Eq : forall Σ iface phi oid t e1 e2 bt,
      type_expr Σ iface phi oid t e1 bt ->
      type_expr Σ iface phi oid t e2 bt ->
      type_expr Σ iface phi oid t (EEq e1 e2) TBool.

(** Mutual induction schemes for type_ref / type_expr *)
Scheme type_ref_ind2 := Induction for type_ref Sort Prop
  with type_expr_ind2 := Induction for type_expr Sort Prop.
Combined Scheme type_ref_expr_mutind from type_ref_ind2, type_expr_ind2.

(* ================================================================= *)
(** ** Mapping Expression Judgment *)
(** Σ; I; Φ ⊢_{⊥?Id} m : μ *)

Inductive type_mapexpr : contract_env -> interface -> list expr -> opt_id ->
                          map_expr -> mapping_type -> Prop :=
  (** T-Exp *)
  | T_Exp : forall Σ iface phi oid e bt,
      type_expr Σ iface phi oid TagU e bt ->
      type_mapexpr Σ iface phi oid (MExp e) (MBase bt)

  (** T-Mapping *)
  | T_Mapping : forall Σ iface phi oid bindings bt mu,
      mapping_type_wf (MMapping bt mu) ->
      Forall (fun p => type_expr Σ iface phi oid TagU (fst p) bt) bindings ->
      Forall (fun p => type_mapexpr Σ iface phi oid (snd p) mu) bindings ->
      type_mapexpr Σ iface phi oid (MMap bindings (MMapping bt mu)) (MMapping bt mu)

  (** T-MappingUpd *)
  | T_MappingUpd : forall Σ iface phi oid r bindings bt mu k,
      type_ref Σ iface phi k oid TagU r (SMapping (MMapping bt mu)) ->
      Forall (fun p => type_expr Σ iface phi oid TagU (fst p) bt) bindings ->
      Forall (fun p => type_mapexpr Σ iface phi oid (snd p) mu) bindings ->
      type_mapexpr Σ iface phi oid (MMapUpd r bindings (MMapping bt mu)) (MMapping bt mu).

(* ================================================================= *)
(** ** Slot Expression Judgment *)
(** Σ; I; Φ ⊢_{⊥?Id} se : σ *)

Inductive type_slotexpr : contract_env -> interface -> list expr -> opt_id ->
                           slot_expr -> slot_type -> Prop :=
  (** T-MapExp *)
  | T_SlotMap : forall Σ iface phi oid m mu,
      type_mapexpr Σ iface phi oid m mu ->
      type_slotexpr Σ iface phi oid (SEMap m) (SMapping mu)

  (** T-SlotBase: base expressions may initialize or update ABI base slots. *)
  | T_SlotBase : forall Σ iface phi oid e bt,
      type_expr Σ iface phi oid TagU e bt ->
      type_slotexpr Σ iface phi oid (SEMap (MExp e)) (SAbi (ABase bt))

  (** T-SlotRef *)
  | T_SlotRef : forall Σ iface phi oid k r a,
      type_ref Σ iface phi k oid TagU r (SContract a) ->
      type_slotexpr Σ iface phi oid (SERef r) (SContract a)

  (** T-SlotAddr *)
  | T_SlotAddr : forall Σ iface phi oid se a,
      type_slotexpr Σ iface phi oid se (SContract a) ->
      type_slotexpr Σ iface phi oid (SEAddr se) (SAbi (AContractAddr a))

  (** T-Create *)
  | T_Create : forall Σ iface phi oid a ctor ses,
      Σ_cnstr Σ a = Some ctor ->
      isPayable ctor = false ->
      Forall2 (fun se alpha => type_slotexpr Σ iface phi oid se (SAbi alpha))
              ses (map snd (ctor_iface ctor)) ->
      (** P4: semantic entailment of constructor preconditions *)
      semantic_entailment_ctor_call Σ iface (ctor_iface ctor) phi oid
        ses zero_callvalue_slot_expr (ctor_iff ctor) ->
      type_slotexpr Σ iface phi oid (SENew a None ses) (SContract a)

  (** T-CreatePayable *)
  | T_CreatePayable : forall Σ iface phi oid a ctor se_val ses,
      Σ_cnstr Σ a = Some ctor ->
      isPayable ctor = true ->
      Forall2 (fun se alpha => type_slotexpr Σ iface phi oid se (SAbi alpha))
              ses (map snd (ctor_iface ctor)) ->
      type_slotexpr Σ iface phi oid se_val (SAbi (ABase (TInt (UintT 256)))) ->
      (** P4: semantic entailment of constructor preconditions *)
      semantic_entailment_ctor_call Σ iface (ctor_iface ctor) phi oid
        ses se_val (ctor_iff ctor) ->
      type_slotexpr Σ iface phi oid (SENew a (Some se_val) ses) (SContract a).

(** Custom induction principle for [type_slotexpr] that gives an IH
    for every element in the [Forall2] premises of T_Create / T_CreatePayable. *)
Section type_slotexpr_ind.

Variable P : contract_env -> interface -> list expr -> opt_id -> slot_expr -> slot_type -> Prop.

Hypothesis H_SlotMap : forall Σ iface phi oid m mu,
  type_mapexpr Σ iface phi oid m mu ->
  P Σ iface phi oid (SEMap m) (SMapping mu).

Hypothesis H_SlotBase : forall Σ iface phi oid e bt,
  type_expr Σ iface phi oid TagU e bt ->
  P Σ iface phi oid (SEMap (MExp e)) (SAbi (ABase bt)).

Hypothesis H_SlotRef : forall Σ iface phi oid k r a,
  type_ref Σ iface phi k oid TagU r (SContract a) ->
  P Σ iface phi oid (SERef r) (SContract a).

Hypothesis H_SlotAddr : forall Σ iface phi oid se a,
  type_slotexpr Σ iface phi oid se (SContract a) ->
  P Σ iface phi oid se (SContract a) ->
  P Σ iface phi oid (SEAddr se) (SAbi (AContractAddr a)).

Hypothesis H_Create : forall Σ iface phi oid a ctor ses,
  Σ_cnstr Σ a = Some ctor ->
  isPayable ctor = false ->
  Forall2 (fun se alpha => type_slotexpr Σ iface phi oid se (SAbi alpha))
          ses (map snd (ctor_iface ctor)) ->
  Forall2 (fun se alpha => P Σ iface phi oid se (SAbi alpha))
          ses (map snd (ctor_iface ctor)) ->
  semantic_entailment_ctor_call Σ iface (ctor_iface ctor) phi oid
    ses zero_callvalue_slot_expr (ctor_iff ctor) ->
  P Σ iface phi oid (SENew a None ses) (SContract a).

Hypothesis H_CreatePayable : forall Σ iface phi oid a ctor se_val ses,
  Σ_cnstr Σ a = Some ctor ->
  isPayable ctor = true ->
  Forall2 (fun se alpha => type_slotexpr Σ iface phi oid se (SAbi alpha))
          ses (map snd (ctor_iface ctor)) ->
  Forall2 (fun se alpha => P Σ iface phi oid se (SAbi alpha))
          ses (map snd (ctor_iface ctor)) ->
  type_slotexpr Σ iface phi oid se_val (SAbi (ABase (TInt (UintT 256)))) ->
  P Σ iface phi oid se_val (SAbi (ABase (TInt (UintT 256)))) ->
  semantic_entailment_ctor_call Σ iface (ctor_iface ctor) phi oid
    ses se_val (ctor_iff ctor) ->
  P Σ iface phi oid (SENew a (Some se_val) ses) (SContract a).

Lemma type_slotexpr_ind2 :
  forall Σ iface phi oid se st,
    type_slotexpr Σ iface phi oid se st -> P Σ iface phi oid se st.
Proof.
  fix IH 7. intros Σ iface phi oid se st Htyp.
  destruct Htyp as [sg0 iface0 phi0 oid0 m mu Hm
                    | sg0 iface0 phi0 oid0 e bt He
                    | sg0 iface0 phi0 oid0 k r a Hr
                    | sg0 iface0 phi0 oid0 se0 a Hse0
                    | sg0 iface0 phi0 oid0 a ctor ses Hcl Hnp Hses HP4
                    | sg0 iface0 phi0 oid0 a ctor se_val ses Hcl Hpay Hses Hval HP4].
  - apply H_SlotMap; exact Hm.
  - apply H_SlotBase; exact He.
  - apply H_SlotRef with (k := k); exact Hr.
  - apply H_SlotAddr; [exact Hse0 | exact (IH _ _ _ _ _ _ Hse0)].
  - assert (HIH : Forall2 (fun se alpha => P sg0 iface0 phi0 oid0 se (SAbi alpha))
               ses (map snd (ctor_iface ctor))).
    { clear Hcl Hnp HP4.
      induction Hses as [|se0 alpha0 rses ralphas Hse0 Hrest IHfa].
      - constructor.
      - constructor; [exact (IH _ _ _ _ _ _ Hse0) | exact IHfa]. }
    exact (H_Create _ _ _ _ _ _ _ Hcl Hnp Hses HIH HP4).
  - assert (HIH : Forall2 (fun se alpha => P sg0 iface0 phi0 oid0 se (SAbi alpha))
               ses (map snd (ctor_iface ctor))).
    { clear Hcl Hpay HP4 Hval.
      induction Hses as [|se0 alpha0 rses ralphas Hse0 Hrest IHfa].
      - constructor.
      - constructor; [exact (IH _ _ _ _ _ _ Hse0) | exact IHfa]. }
    exact (H_CreatePayable _ _ _ _ _ _ _ _ Hcl Hpay Hses HIH Hval
             (IH _ _ _ _ _ _ Hval) HP4).
Qed.

End type_slotexpr_ind.

(* ================================================================= *)
(** ** Create Judgment *)
(** Σ; I; Φ ⊢_Id creates : C *)

Inductive type_creates : contract_env -> interface -> list expr -> opt_id ->
                          list create -> storage_layout -> Prop :=
  | T_Creates : forall Σ iface phi oid creates layout,
      (* C = {x₁ : σ₁, ..., xₙ : σₙ} *)
      layout = map (fun c => (snd (fst c), fst (fst c))) creates ->
      (* balance : uint256 ∈ C *)
      alist_lookup layout "balance"%string = Some (SAbi (ABase (TInt (UintT 256)))) ->
      (* ∀ i. Σ ⊢ σᵢ wf *)
      Forall (fun c => slot_type_wf Σ (fst (fst c))) creates ->
      (* ∀ i. Σ; I; Φ ⊢_⊥ seᵢ : σᵢ *)
      Forall (fun c => type_slotexpr Σ iface phi ONone (snd c) (fst (fst c))) creates ->
      type_creates Σ iface phi oid creates layout.

(* ================================================================= *)
(** ** Update Judgment *)
(** Σ; I; Φ ⊢_Id update *)

Inductive type_update : contract_env -> interface -> list expr -> opt_id ->
                         update -> Prop :=
  | T_Update : forall Σ iface phi oid r se sty,
      type_ref Σ iface phi TagS oid TagU r sty ->
      type_slotexpr Σ iface phi oid se sty ->
      type_update Σ iface phi oid (r, se).

(** Σ; I; Φ ⊢_Id updates *)
Inductive type_updates : contract_env -> interface -> list expr -> opt_id ->
                          list update -> Prop :=
  | T_Updates : forall Σ iface phi oid upds,
      Forall (fun u => type_update Σ iface phi oid u) upds ->
      (* no-overlap condition: ¬(refⱼ ⪯_specific refᵢ) *)
      (forall i j, i < length upds -> j < i ->
        ~ more_specific_eq (fst (nth j upds (RVar ""%string, SEMap (MExp (EBool false)))))
                           (fst (nth i upds (RVar ""%string, SEMap (MExp (EBool false)))))) ->
      type_updates Σ iface phi oid upds.

(* ================================================================= *)
(** ** Return Expression Judgment *)
(** Σ; I; Φ ⊢_{⊥?Id,t} ret : α? *)

Definition return_abi_base_type (alpha : abi_type) : base_type :=
  match alpha with
  | ABase bt => bt
  | AContractAddr _ => TAddress
  end.

Definition type_return_expr (Σ : contract_env) (iface : interface)
    (phi : list expr) (oid : opt_id) (t : time_tag)
    (ret : option expr) (ret_ty : option abi_type) : Prop :=
  match ret, ret_ty with
  | None, None => True
  | Some e, Some alpha => type_expr Σ iface phi oid t e (return_abi_base_type alpha)
  | _, _ => False
  end.

(* ================================================================= *)
(** ** Constructor Judgment *)
(** Σ ⊢_Id cnstr : C *)

Inductive type_constructor : contract_env -> ident -> constructor ->
                              storage_layout -> Prop :=
  | T_Ctor : forall Σ a ctor layout,
      (* Σ ⊢ I wf *)
      interface_wf Σ (ctor_iface ctor) ->
      (* preconditions well-typed *)
      Forall (fun pre => type_expr Σ (ctor_iface ctor) empty_phi ONone TagU pre TBool)
             (ctor_iff ctor) ->
      (* case conditions well-typed *)
      Forall (fun cc => type_expr Σ (ctor_iface ctor) empty_phi ONone TagU (fst cc) TBool)
             (ctor_cases ctor) ->
      (* creates well-typed *)
      Forall (fun cc =>
        type_creates Σ (ctor_iface ctor) (case_phi (ctor_iff ctor) (fst cc))
          (OSome a) (snd cc) layout)
             (ctor_cases ctor) ->
      (* all slot types in C are well-formed *)
      Forall (fun p => slot_type_wf Σ (snd p)) layout ->
      (* dom(C) ∩ dom(I) = ∅ *)
      (forall x, alist_dom layout x -> ~ alist_dom (ctor_iface ctor) x) ->
      (* postconditions well-typed under Σ' = Σ with {Storage = (Σ_Storage, Id : C)} *)
      let Σ' := Σ_with_storage Σ a layout in
      Forall (fun post => type_expr Σ' (ctor_iface ctor) empty_phi (OSome a) TagU post TBool)
             (ctor_post ctor) ->
      (* case consistency: exactly one case is true when preconditions hold *)
      semantic_entailment Σ (ctor_iface ctor) (ctor_iff ctor) ONone
        (case_consistency_exprs (ctor_case_conditions (ctor_cases ctor))) ->
      type_constructor Σ a ctor layout.

(* ================================================================= *)
(** ** Transition Judgment *)
(** Σ ⊢_Id trans *)

Inductive type_transition : contract_env -> ident -> transition -> Prop :=
  | T_Trans : forall Σ a tr,
      (* Σ ⊢ I wf *)
      interface_wf Σ (trans_iface tr) ->
      (* preconditions well-typed *)
      Forall (fun pre => type_expr Σ (trans_iface tr) empty_phi (OSome a) TagU pre TBool)
             (trans_iff tr) ->
      (* case conditions well-typed *)
      Forall (fun tc => type_expr Σ (trans_iface tr) empty_phi (OSome a) TagU (tc_cond tc) TBool)
             (trans_cases tr) ->
      (* updates well-typed *)
      Forall (fun tc =>
        type_updates Σ (trans_iface tr) (case_phi (trans_iff tr) (tc_cond tc))
          (OSome a) (tc_updates tc))
             (trans_cases tr) ->
      (* returns well-typed *)
      Forall (fun tc => type_return_expr Σ (trans_iface tr) empty_phi (OSome a) TagT
                        (tc_return tc) (trans_rettype tr))
             (trans_cases tr) ->
      (* postconditions well-typed *)
      Forall (fun post => type_expr Σ (trans_iface tr) empty_phi (OSome a) TagT post TBool)
             (trans_post tr) ->
      (* case consistency: exactly one case is true when preconditions hold *)
      semantic_entailment Σ (trans_iface tr) (trans_iff tr) (OSome a)
        (case_consistency_exprs (trans_case_conditions (trans_cases tr))) ->
      type_transition Σ a tr.

(* ================================================================= *)
(** ** Well-typed Σ (Definition 6.1) *)

(** S1: for every A ∈ dom(Σ_Cnstr) exists Σ' ⊆ Σ well-typed,
        such that Σ' ⊢_A Σ_Cnstr(A) : Σ_Storage(A)
    S2: for every A ∈ dom(Σ_Trans) exists Σ' ⊆ Σ well-typed,
        such that ∀ trans ∈ Σ_Trans(A). Σ' ⊢_A trans *)
Inductive Σ_well_typed : contract_env -> Prop :=
  | Σ_WT : forall Σ,
      (* S0: all storage layouts have well-formed slot types *)
      (forall a layout, Σ_storage Σ a = Some layout ->
        Forall (fun p => slot_type_wf Σ (snd p)) layout) ->
      (* S1: constructors *)
      (forall a ctor,
        Σ_cnstr Σ a = Some ctor ->
        exists Σ' layout,
          Σ_incl Σ' Σ /\
          Σ_cnstr Σ' a = None /\
          Σ_cnstr_size Σ' < Σ_cnstr_size Σ /\
          Σ_well_typed Σ' /\
          type_constructor Σ' a ctor layout /\
          Σ_storage Σ a = Some layout) ->
      (* S2: transitions *)
      (forall a transs,
        Σ_trans Σ a = Some transs ->
        exists Σ',
          Σ_incl Σ' Σ /\ Σ_well_typed Σ' /\
          Forall (fun tr => type_transition Σ' a tr) transs) ->
      Σ_well_typed Σ.

(* ================================================================= *)
(** ** Contract Judgment *)
(** Σ ⊢ contract : Σ' *)

Inductive type_contract : contract_env -> contract -> contract_env -> Prop :=
  | T_Contract : forall Σ c layout,
      let a := contract_name c in
      let ctor := contract_ctor c in
      let transs := contract_trans c in
      let invs := contract_inv c in
      (* freshness: contract name not already in Σ *)
      ~ dom (Σ_storage Σ) a ->
      ~ dom (Σ_cnstr Σ) a ->
      ~ dom (Σ_trans Σ) a ->
      (* Σ ⊢_Id cnstr : C *)
      type_constructor Σ a ctor layout ->
      (* Σ' = Σ with {Storage, Cnstr} *)
      let Σ' := Σ_with_cnstr (Σ_with_storage Σ a layout) a ctor in
      (* ∀ trans. Σ' ⊢_Id trans *)
      Forall (fun tr => type_transition Σ' a tr) transs ->
      (* invariants well-typed *)
      Forall (fun inv => type_expr Σ' (ctor_iface ctor) empty_phi (OSome a) TagU inv TBool) invs ->
      (* Σ'' = Σ' with {Trans} *)
      let Σ'' := Σ_with_trans Σ' a transs in
      type_contract Σ c Σ''.

(* ================================================================= *)
(** ** Spec Judgment *)
(** Σ ⊢ spec : Σ' *)

Inductive type_spec_from : spec -> contract_env -> contract_env -> Prop :=
  | T_SpecFromNil : forall Σ,
      type_spec_from [] Σ Σ
  | T_SpecFromCons : forall c rest Σ Σ' Σ'',
      type_contract Σ c Σ' ->
      type_spec_from rest Σ' Σ'' ->
      type_spec_from (c :: rest) Σ Σ''.

(** ⊢ spec : Σ *)
Definition type_spec (sp : spec) (Σ : contract_env) : Prop :=
  type_spec_from sp Σ_empty Σ.
